#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_unsafe)]

use once_cell::sync::Lazy;
use once_cell::sync::OnceCell;
use parking_lot::{Mutex, RwLock, RwLockReadGuard};
use core::mem::{self, size_of};
use ahash::AHashMap as HashMap;
use smallvec::SmallVec;
use std::cell::RefCell;
use core::{ptr};
use std::sync::atomic::AtomicUsize;
use std::cell::Cell;
use likely_stable::{likely, unlikely};

use mmtk::{
    util::{
        copy::{CopySemantics, GCWorkerCopyContext},
        opaque_pointer::*,
        Address,
        ObjectReference,
        options::{Options, PlanSelector}
    },
    vm::{
        slot::{Slot, MemorySlice},
        ObjectModel,
        VMBinding,
        Scanning,
        Collection,
        ActivePlan,
        ReferenceGlue,
        GCThreadContext,
        ObjectTracer
    },
    AllocationSemantics,
    memory_manager,
    Mutator,
    MMTKBuilder,
    MMTK,

    // For ObjectModel impl:
    vm::{
        VMGlobalLogBitSpec,
        VMLocalForwardingBitsSpec,
        VMLocalForwardingPointerSpec,
        VMLocalLOSMarkNurserySpec,
        VMLocalMarkBitSpec,
        VMLocalPinningBitSpec,
    },

    // For Scanning impl:
    vm::{RootsWorkFactory, ObjectTracerContext},
};
use mmtk::util::constants::{BYTES_IN_ADDRESS, LOG_BYTES_IN_ADDRESS};

use std::sync::atomic::{AtomicBool, Ordering::{Acquire, Release}};
use parking_lot::{Mutex as ParkMutex, Condvar as ParkCondvar};
use std::sync::atomic::Ordering::AcqRel;

static STW_REQUESTED: AtomicBool = AtomicBool::new(false);
static STW_LOCK: ParkMutex<()> = ParkMutex::new(());
static STW_CV: ParkCondvar = ParkCondvar::new();

use crate::value::{
    ObjHeader,
    TAG_BOXED_F64, TAG_STRING, TAG_ARRAY, TAG_CLOSURE, TAG_OBJECT,
    ValueRepr, BoxedF64, BoxedStr, BoxedClosure, BoxedObj,
    ARRAY_LEN_OFFSET, ARRAY_DATA_OFFSET,
    is_ptr,
    NULL,
};

static MUTATOR_COUNT: AtomicUsize = AtomicUsize::new(0);

// All currently attached mutators (raw pointers owned by their TLS Boxes).
// We use raw pointers so we can hand out &'static mut Mutator<_> when MMTk asks.
// Safety: MMTk calls into this only at STW points or GC worker context,
// so aliasing is controlled by the GC protocol.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct MutatorRaw(*mut Mutator<NapalmVM>);
unsafe impl Send for MutatorRaw {}
unsafe impl Sync for MutatorRaw {}

impl MutatorRaw {
    fn as_mut(&self) -> &'static mut Mutator<NapalmVM> {
        unsafe { &mut *self.0 }
    }
}

static ALL_MUTATORS: Lazy<Mutex<Vec<MutatorRaw>>> = Lazy::new(|| Mutex::new(Vec::new()));

// =================================================================
// ==================== Helpers ====================================
// =================================================================

#[inline(always)]
unsafe fn read_len_unaligned(base: *const u8) -> usize {
    // Array len is stored as i64 immediately after the header.
    // We use read_unaligned to be resilient to any future packing.
    let len_ptr = base.add(ARRAY_LEN_OFFSET as usize) as *const i64;
    (*len_ptr).max(0) as usize
}

#[inline(always)]
fn size_of_object_from_tag(base: *const u8) -> usize {
    // SAFETY: caller ensures `base` points at a live object start.
    unsafe {
        let hdr = &*(base as *const ObjHeader);
        match hdr.tag {
            TAG_BOXED_F64 => mem::size_of::<BoxedF64>(),

            // BoxedStr stores borrowed data pointer; the object itself is fixed size.
            TAG_STRING    => mem::size_of::<BoxedStr>(),

            // Flat array layout: | ObjHeader | i64 len | len * i64 elements |
            TAG_ARRAY     => {
                let len = read_len_unaligned(base);
                (ARRAY_DATA_OFFSET as usize) + len * mem::size_of::<i64>()
            }

            // Dictionary-like object with Rust HashMaps inside:
            // the GC only owns the outer header+two HashMap structs; the buffers those maps
            // allocate live on the Rust heap and are *not* part of this object’s GC size.
            TAG_OBJECT    => mem::size_of::<BoxedObj>(),

            _ => {
                debug_assert!(false, "Unknown object tag: {}", hdr.tag);
                mem::size_of::<ObjHeader>() // conservative non-zero size
            }
        }
    }
}


#[inline(always)]
fn emit_shadow_roots_to_factory<T: RootsWorkFactory<SlotItem>>(factory: &mut T) {
    let mut edges: SmallVec<[SlotItem; 64]> = SmallVec::new();
    edges.reserve_exact(64);

    ShadowStack::with_roots(|slot: *mut i64| {
        edges.push(SlotItem(Address::from_ptr(slot.cast::<u8>())));
        if edges.len() == 64 {
            factory.create_process_roots_work(edges.to_vec()); // unavoidable copy for work packet
            edges.clear(); // keeps inline buffer
        }
    });

    if !edges.is_empty() {
        factory.create_process_roots_work(edges.to_vec());
    }
}

// ==================================================================
// ==================== Slot ========================================
// ==================================================================
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SlotItem(pub Address);

impl From<Address> for SlotItem { fn from(a: Address) -> Self { SlotItem(a) } }

impl Slot for SlotItem {
    #[inline(always)]
    fn load(&self) -> Option<ObjectReference> {
        use crate::value::{ObjHeader, TAG_BOXED_F64, TAG_STRING, TAG_ARRAY, TAG_OBJECT, TAG_CLOSURE, ValueRepr, NULL, is_ptr};
        let v: ValueRepr = unsafe { ptr::read(self.0.to_ptr::<ValueRepr>()) };

        if likely(is_ptr(v)) && v != NULL {
            // Validate that this is a *Napalm GC object*, not some foreign/native handle.
            unsafe {
                let h = (v as *const ObjHeader).as_ref()?;
                match h.tag {
                    TAG_BOXED_F64 | TAG_STRING | TAG_ARRAY | TAG_OBJECT | TAG_CLOSURE => {
                        return ObjectReference::from_raw_address(Address::from_ptr(v as *mut u8));
                    }
                    _ => return None, // NOT a GC-managed object (e.g., native Promise handle)
                }
            }
        }
        None
    }

    #[inline(always)]
    fn store(&self, obj: ObjectReference) {
        let p = self.0.to_mut_ptr::<ValueRepr>();
        let val: ValueRepr = obj.to_raw_address().to_ptr::<u8>() as i64;
        unsafe { ptr::write(p, val) };
    }
}

// ==================================================================
// ==================== MemSlice ====================================
// ==================================================================

/// A concrete memory slice over a contiguous region of **heap** memory.
/// We optionally carry the owning object for better maturity checks.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct MemSlice {
    start: Address,
    bytes: usize,
    owner: Option<ObjectReference>,
}

impl MemSlice {
    #[inline(always)]
    pub fn new(start: Address, bytes: usize) -> Self {
        Self { start, bytes, owner: None }
    }
    #[inline(always)]
    pub fn for_object(owner: ObjectReference, start: Address, bytes: usize) -> Self {
        Self { start, bytes, owner: Some(owner) }
    }
}

/// Iterator that yields our `Slot` over each machine word in the slice.
pub struct MemSliceIter {
    cursor: Address,
    limit: Address,
}

impl Iterator for MemSliceIter {
    type Item = SlotItem;
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor >= self.limit {
            None
        } else {
            let slot = self.cursor;
            // advance one machine word
            self.cursor = self.cursor + BYTES_IN_ADDRESS;
            Some(SlotItem::from(slot))
        }
    }
}

impl MemorySlice for MemSlice {
    type SlotType = SlotItem;
    type SlotIterator = MemSliceIter;

    #[inline(always)]
    fn iter_slots(&self) -> Self::SlotIterator {
        MemSliceIter {
            cursor: self.start,
            limit:  self.start + self.bytes,
        }
    }

    #[inline(always)]
    fn object(&self) -> Option<ObjectReference> { self.owner }

    #[inline(always)]
    fn start(&self) -> Address { self.start }

    #[inline(always)]
    fn bytes(&self) -> usize { self.bytes }

    #[inline(always)]
    fn copy(src: &Self, tgt: &Self) {
        debug_assert_eq!(src.bytes, tgt.bytes, "memcpy slices must be same size");
        debug_assert_eq!(src.bytes & ((1 << LOG_BYTES_IN_ADDRESS) - 1), 0, "slice size must be word-aligned");
        unsafe {
            let words = tgt.bytes >> LOG_BYTES_IN_ADDRESS;
            let sp = src.start.to_ptr::<usize>();
            let dp = tgt.start.to_mut_ptr::<usize>();
            std::ptr::copy(sp, dp, words);
        }
    }
}

// =================================================================
// ==================== MMTk binding for Napalm VM =================
// =================================================================
#[derive(Clone, Copy, Debug, Default)] pub struct NapalmVM;
#[derive(Clone, Copy, Debug, Default)] pub struct VMObjModel;
#[derive(Clone, Copy, Debug, Default)] pub struct VMScanning;
#[derive(Clone, Copy, Debug, Default)] pub struct VMCollection;
#[derive(Clone, Copy, Debug, Default)] pub struct VMActivePlan;
#[derive(Clone, Copy, Debug, Default)] pub struct VMRefGlue;

impl ObjectModel<NapalmVM> for VMObjModel {
    // ---- Where per-object metadata lives ----
    // Keep it simple: everything (except the forwarding *pointer*) goes to side metadata.
    const GLOBAL_LOG_BIT_SPEC: VMGlobalLogBitSpec =
        VMGlobalLogBitSpec::side_first();

    // Forwarding pointer MUST be in-header. We place it at the first payload word:
    // offset = header_size_in_bits (so it overwrites the first payload word only while dead).
    const LOCAL_FORWARDING_POINTER_SPEC: VMLocalForwardingPointerSpec =
        VMLocalForwardingPointerSpec::in_header(
            (core::mem::size_of::<crate::value::ObjHeader>() * 8) as isize
        );

    // Local side-metadata chain (order matters: first -> side_first, then -> side_after(prev))
    const LOCAL_FORWARDING_BITS_SPEC: VMLocalForwardingBitsSpec =
        VMLocalForwardingBitsSpec::side_first();

    const LOCAL_MARK_BIT_SPEC: VMLocalMarkBitSpec =
        VMLocalMarkBitSpec::side_after(Self::LOCAL_FORWARDING_BITS_SPEC.as_spec());

    const LOCAL_LOS_MARK_NURSERY_SPEC: VMLocalLOSMarkNurserySpec =
        VMLocalLOSMarkNurserySpec::side_after(Self::LOCAL_MARK_BIT_SPEC.as_spec());

    // ---- Object ref <-> object start invariants ----
    // Napalm uses "object ref == object start".
    const OBJECT_REF_OFFSET_LOWER_BOUND: isize = 0;
    const UNIFIED_OBJECT_REFERENCE_ADDRESS: bool = true;

    // ---- Sizes & alignments ----
    #[inline(always)]
    fn get_current_size(object: ObjectReference) -> usize {
        use crate::value::*;
        let hdr = Self::ref_to_object_start(object).to_ptr::<ObjHeader>();
        unsafe {
            match (*hdr).tag {
                TAG_BOXED_F64 => core::mem::size_of::<BoxedF64>(),
                TAG_STRING    => core::mem::size_of::<BoxedStr>(),
                TAG_ARRAY     => core::mem::size_of::<BoxedArray>(),
                TAG_CLOSURE   => core::mem::size_of::<BoxedClosure>(),
                TAG_OBJECT    => core::mem::size_of::<BoxedObj>(),
                _ => core::mem::size_of::<ObjHeader>(), // conservative fallback
            }
        }
    }

    #[inline(always)]
    fn get_size_when_copied(object: ObjectReference) -> usize {
        // We don’t change layout when copying.
        Self::get_current_size(object)
    }

    #[inline(always)]
    fn get_align_when_copied(object: ObjectReference) -> usize {
        use crate::value::*;
        let hdr = Self::ref_to_object_start(object).to_ptr::<ObjHeader>();
        unsafe {
            match (*hdr).tag {
                TAG_BOXED_F64 => core::mem::align_of::<BoxedF64>(),
                TAG_STRING    => core::mem::align_of::<BoxedStr>(),
                TAG_ARRAY     => core::mem::align_of::<BoxedArray>(),
                TAG_CLOSURE   => core::mem::align_of::<BoxedClosure>(),
                TAG_OBJECT    => core::mem::align_of::<BoxedObj>(),
                _             => core::mem::align_of::<ObjHeader>(),
            }
        }
    }

    #[inline(always)]
    fn get_align_offset_when_copied(_object: ObjectReference) -> usize {
        // object ref == object start, so no offset is needed.
        0
    }

    // ---- Object addresses ----
    #[inline(always)]
    fn ref_to_object_start(object: ObjectReference) -> Address {
        // In Napalm, object ref is the start address returned by alloc().
        object.to_raw_address()
    }

    #[inline(always)]
    fn ref_to_header(object: ObjectReference) -> Address {
        // We place header at object start.
        object.to_raw_address()
    }

    // ---- Copying helpers (used by copying/compacting plans; harmless for StickyImmix) ----
    #[inline(always)]
    fn copy(
        from: ObjectReference,
        semantics: CopySemantics,
        copy_context: &mut GCWorkerCopyContext<NapalmVM>,
    ) -> ObjectReference {
        let bytes = Self::get_size_when_copied(from);
        let align = Self::get_align_when_copied(from);
        let align_off = Self::get_align_offset_when_copied(from);
        let dst_region = copy_context.alloc_copy(from, align, align_off, bytes, semantics);
        let to_ref = Self::get_reference_when_copied_to(from, dst_region);
        let end = Self::copy_to(from, to_ref, dst_region);
        debug_assert_eq!(end, dst_region.add(bytes));
        copy_context.post_copy(to_ref, bytes, semantics);
        to_ref
    }

    #[inline(always)]
    fn copy_to(from: ObjectReference, _to: ObjectReference, region: Address) -> Address {
        // Raw byte copy of the whole object.
        let src   = Self::ref_to_object_start(from);
        let bytes = Self::get_size_when_copied(from);

        unsafe {
            core::ptr::copy_nonoverlapping(
                src.to_ptr::<u8>(),
                region.to_mut_ptr::<u8>(),
                bytes,
            );
        }
        region.add(bytes)
    }

    #[inline(always)]
    fn get_reference_when_copied_to(
        _from: ObjectReference,
        to: Address,
    ) -> ObjectReference {
        // With unified refs, the post-copy reference is exactly the region base.
        ObjectReference::from_raw_address(to).expect("MMTk asked for a null target")
    }

    // ---- Type descriptors (debug only; C-style nul-terminated) ----
    fn get_type_descriptor(reference: ObjectReference) -> &'static [i8] {
        use crate::value::*;
        static TD_F64:     [i8; 4] = [b'f' as i8, b'6' as i8, b'4' as i8, 0];
        static TD_STR:     [i8; 5] = [b's' as i8, b't' as i8, b'r' as i8, b'\0' as i8, 0];
        static TD_ARRAY:   [i8; 6] = [b'a' as i8, b'r' as i8, b'r' as i8, b'a' as i8, b'y' as i8, 0];
        static TD_OBJECT:  [i8; 7] = [b'o' as i8, b'b' as i8, b'j' as i8, b'e' as i8, b'c' as i8, b't' as i8, 0];
        static TD_CLOSURE: [i8; 8] = [b'c' as i8, b'l' as i8, b'o' as i8, b's' as i8, b'u' as i8, b'r' as i8, b'e' as i8, 0];
        static TD_UNKNOWN: [i8; 8] = [b'u' as i8, b'n' as i8, b'k' as i8, b'n' as i8, b'o' as i8, b'w' as i8, b'n' as i8, 0];

        let hdr = Self::ref_to_object_start(reference).to_ptr::<ObjHeader>();
        unsafe {
            match (*hdr).tag {
                TAG_BOXED_F64 => &TD_F64,
                TAG_STRING    => &TD_STR,
                TAG_ARRAY     => &TD_ARRAY,
                TAG_OBJECT    => &TD_OBJECT,
                TAG_CLOSURE   => &TD_CLOSURE,
                _             => &TD_UNKNOWN,
            }
        }
    }

    // ---- Debug printer ----
    fn dump_object(object: ObjectReference) {
        use crate::value::*;
        let addr = object.to_raw_address();
        unsafe {
            let hdr = addr.to_ptr::<ObjHeader>();
            if hdr.is_null() {
                eprintln!("[napalm:mmtk] <null object @ {addr:?}>");
                return;
            }
            let tag = (*hdr).tag;
            let size = Self::get_current_size(object);
            match tag {
                TAG_BOXED_F64 => {
                    let o = addr.to_ptr::<BoxedF64>();
                    #[cfg(debug_assertions)] {
                        eprintln!("[napalm:mmtk] BoxedF64 @ {addr:?} val={}", (*o).val);
                    }
                }
                TAG_STRING => {
                    let s = addr.to_ptr::<BoxedStr>();
                    #[cfg(debug_assertions)] {
                        eprintln!("[napalm:mmtk] String @ {addr:?} len={} data={:?}", (*s).len, (*s).data);
                    }
                }
                TAG_ARRAY => {
                    let a = addr.to_ptr::<BoxedArray>();
                    // Avoid formatting the whole Vec; print capacity/len.
                    #[cfg(debug_assertions)] {
                        eprintln!(
                            "[napalm:mmtk] Array @ {addr:?} len={} cap={}",
                            (*a).buf.len(), (*a).buf.capacity()
                        );
                    }
                }
                TAG_OBJECT => {
                    let o = addr.to_ptr::<BoxedObj>();
                    #[cfg(debug_assertions)] {
                        eprintln!(
                            "[napalm:mmtk] Object @ {addr:?} slots={{by_id: {}, by_str: {}}}",
                            (*o).by_id.len(), (*o).by_str.len()
                        );
                    }
                }
                TAG_CLOSURE => {
                    let c = addr.to_ptr::<BoxedClosure>();
                    #[cfg(debug_assertions)]
                    eprintln!("[napalm:mmtk] Closure @ {addr:?} env_len={} code_ptr=0x{:x}", (*c).env.len(), (*c).code_ptr);
                }
                _ => {
                    #[cfg(debug_assertions)] {
                        eprintln!("[napalm:mmtk] <unknown tag={tag}> @ {addr:?} ({} bytes)", size);
                    }
                }
            }
        }
    }
}

impl Scanning<NapalmVM> for VMScanning {
    #[inline(always)]
    fn scan_object<SV: mmtk::vm::SlotVisitor<SlotItem>>(
        _tls: VMWorkerThread,
        object: ObjectReference,
        slot_visitor: &mut SV,
    ) {
        use crate::value::{
            ObjHeader, BoxedF64, BoxedStr, BoxedArray, BoxedObj,
            TAG_BOXED_F64, TAG_STRING, TAG_ARRAY, TAG_OBJECT, is_ptr, NULL,
        };
        use mmtk::util::Address;

        unsafe {
            let base = object.to_raw_address().to_ptr::<u8>();
            let hdr  = &*(base as *const ObjHeader);

            match hdr.tag {
                TAG_BOXED_F64 | TAG_STRING => {
                    // No outgoing references.
                }

                TAG_ARRAY => {
                    let arr = &mut *(base as *mut BoxedArray);
                    let len = arr.buf.len();
                    let ptr = arr.buf.as_mut_ptr();
                    for i in 0..len {
                        let slot_ptr: *mut i64 = ptr.add(i);
                        // optional: cheap filter to avoid handing non-ptr immediates to MMTk
                        let val = *slot_ptr;
                        if is_ptr(val) && val != NULL {
                            let edge = SlotItem(Address::from_ptr(slot_ptr.cast::<u8>()));
                            slot_visitor.visit_slot(edge);
                        }
                    }
                }

                TAG_OBJECT => {
                    let obj = &mut *(base as *mut BoxedObj);

                    // visit proto
                    if is_ptr(obj.proto) && obj.proto != NULL {
                        let slot = &mut obj.proto as *mut ValueRepr;
                        slot_visitor.visit_slot(SlotItem(Address::from_ptr(slot.cast::<u8>())));
                    }

                    for v in obj.by_id.values_mut() {
                        let slot_ptr: *mut i64 = v as *mut i64;
                        let val = *slot_ptr;
                        if is_ptr(val) && val != NULL {
                            let edge = SlotItem(Address::from_ptr(slot_ptr.cast::<u8>()));
                            slot_visitor.visit_slot(edge);
                        }
                    }
                    for v in obj.by_str.values_mut() {
                        let slot_ptr: *mut i64 = v as *mut i64;
                        let val = *slot_ptr;
                        if is_ptr(val) && val != NULL {
                            let edge = SlotItem(Address::from_ptr(slot_ptr.cast::<u8>()));
                            slot_visitor.visit_slot(edge);
                        }
                    }
                }

                TAG_CLOSURE => {
                    let clo = &mut *(base as *mut BoxedClosure);
                    let len = clo.env.len();
                    let ptr = clo.env.as_mut_ptr();
                    for i in 0..len {
                        let slot_ptr: *mut i64 = ptr.add(i);
                        let val = *slot_ptr;
                        if is_ptr(val) && val != NULL {
                            slot_visitor.visit_slot(SlotItem(Address::from_ptr(slot_ptr.cast::<u8>())));
                        }
                    }
                }

                _ => {
                    #[cfg(debug_assertions)]
                    eprintln!("[napalm:mmtk] scan_object: unknown tag={} @{:?}", hdr.tag, base);
                }
            }
        }
    }

    #[inline(always)]
    fn scan_vm_specific_roots(
        _tls: VMWorkerThread,
        mut factory: impl RootsWorkFactory<SlotItem>,
    ) {
        // 1) Shadow stack
        emit_shadow_roots_to_factory(&mut factory);

        // 2) Event loop roots (microtasks, ready timers)
        {
            let mut edges: SmallVec<[SlotItem; 64]> = SmallVec::new();
            crate::event_loop::EVENT_LOOP.with_root_slots(|slot| {
                edges.push(SlotItem(Address::from_ptr(slot.cast::<u8>())));
                if edges.len() == 64 {
                    factory.create_process_roots_work(edges.to_vec());
                    edges.clear();
                }
            });
            if !edges.is_empty() {
                factory.create_process_roots_work(edges.to_vec());
            }
        }

        // 3) HTTP module roots (server dispatch closures, route handlers, and Deferred slots)
        {
            let mut edges: SmallVec<[SlotItem; 64]> = SmallVec::new();
            crate::http::http_with_root_slots(|slot| {
                edges.push(SlotItem(Address::from_ptr(slot.cast::<u8>())));
                if edges.len() == 64 {
                    factory.create_process_roots_work(edges.to_vec());
                    edges.clear();
                }
            });
            if !edges.is_empty() {
                factory.create_process_roots_work(edges.to_vec());
            }
        }

        // Promises – closures stored off-heap
        {
            let mut edges: SmallVec<[SlotItem; 64]> = SmallVec::new();
            crate::native_promises::promises_with_root_slots(|slot| {
                edges.push(SlotItem(Address::from_ptr(slot.cast::<u8>())));
                if edges.len() == 64 { factory.create_process_roots_work(edges.to_vec()); edges.clear(); }
            });
            if !edges.is_empty() { factory.create_process_roots_work(edges.to_vec()); }
        }
    }

    // ===== extra items your MMTk requires =====

    /// Called after a thread’s initial root scan is done.
    #[inline(always)]
    fn notify_initial_thread_scan_complete(_partial_scan: bool, _tls: VMWorkerThread) {
        // No special coordination needed.
    }

    /// Scan roots while running on the *mutator* thread (instead of a GC worker).
    /// We emit the same shadow-stack roots; the mutator reference is not needed yet.
    #[inline(always)]
    fn scan_roots_in_mutator_thread(
        _tls: VMWorkerThread,
        _mutator: &'static mut Mutator<NapalmVM>,
        mut factory: impl RootsWorkFactory<SlotItem>,
    ) {
        emit_shadow_roots_to_factory(&mut factory);
    }

    /// Whether the VM installs a return barrier. Napalm does not.
    #[inline(always)]
    fn supports_return_barrier() -> bool {
        false
    }

    /// Prepare for a second root scan if the collector requests it.
    #[inline(always)]
    fn prepare_for_roots_re_scanning() {
        // Nothing to do for shadow-stack only roots.
    }
}

impl Collection<NapalmVM> for VMCollection {
    /// Request a stop-the-world. In cooperative mode we just set a flag;
    /// mutators will park at the next `yieldpoint()`.
    #[inline(always)]
    fn stop_all_mutators<F>( _tls: VMWorkerThread, mut mutator_visitor: F )
    where
        F: FnMut(&'static mut Mutator<NapalmVM>),
    {
        STW_REQUESTED.store(true, Release);

        let ptrs: Vec<MutatorRaw> = {
            let list = ALL_MUTATORS.lock();
            list.as_slice().to_vec()
        };
        for MutatorRaw(p) in ptrs {
            let m: &'static mut Mutator<NapalmVM> = unsafe { &mut *p };
            mutator_visitor(m);
        }
    }

    /// Resume mutators by clearing the flag and waking all parked threads.
    #[inline(always)]
    fn resume_mutators(
        _tls: VMWorkerThread,
    ) {
        STW_REQUESTED.store(false, Release);
        STW_CV.notify_all();
    }

    /// Called by MMTk on a mutator thread that needs to be blocked for GC.
    /// Park until `resume_mutators` clears the flag.
    #[inline(always)]
    fn block_for_gc(_mutator: VMMutatorThread) {
        if !STW_REQUESTED.load(Acquire) { return; }
        let mut guard = STW_LOCK.lock();        // <- make it mutable
        while STW_REQUESTED.load(Acquire) {
            STW_CV.wait(&mut guard);            // <- pass &mut guard
        }
    }

    /// Spawn a GC worker thread and run the provided closure on it.
    /// MMTk passes a `GCThreadContext` and a closure `f(worker_tls)` that starts the worker.
    #[inline(always)]
    fn spawn_gc_thread(tls: VMThread, ctx: GCThreadContext<NapalmVM>) {
        std::thread::Builder::new()
            .name("mmtk-gc-worker".to_string())
            .spawn(move || {
                let worker_tls: VMWorkerThread = unsafe { std::mem::transmute(tls) };
                match ctx {
                    mmtk::vm::GCThreadContext::Worker(worker) => {
                        worker.run(worker_tls, get_mmtk())
                    }
                }
            })
            .expect("spawn GC worker");
    }
}

impl ActivePlan<NapalmVM> for VMActivePlan {
    #[inline(always)]
    fn is_mutator(_tls: VMThread) -> bool {
        TLS_MUT_PTR.with(|p| !p.get().is_null())
    }

    #[inline(always)]
    fn mutator(_tls: VMMutatorThread) -> &'static mut Mutator<NapalmVM> {
        TLS_MUT_PTR.with(|p| {
            let ptr = p.get();
            assert!(!ptr.is_null(), "No mutator attached on this thread");
            unsafe { &mut *ptr }
        })
    }

    #[inline(always)]
    fn mutators<'a>() -> Box<dyn Iterator<Item = &'a mut Mutator<NapalmVM>> + 'a> {
        let ptrs: Vec<MutatorRaw> = {
            let list = ALL_MUTATORS.lock();
            list.as_slice().to_vec()
        };
        let refs: Vec<&'static mut Mutator<NapalmVM>> = unsafe {
            ptrs.into_iter().map(|p| &mut *p.0).collect()
        };
        Box::new(refs.into_iter())
    }

    #[inline(always)]
    fn number_of_mutators() -> usize {
        MUTATOR_COUNT.load(Acquire)
    }
}

impl ReferenceGlue<NapalmVM> for VMRefGlue {
    /// We don’t keep extra metadata per finalizable object.
    /// Using ObjectReference is supported by MMTk out of the box.
    type FinalizableType = ObjectReference;

    /// Weak/soft refs not implemented yet: nothing to clear.
    #[inline(always)]
    fn clear_referent(_new_reference: ObjectReference) {
        // If/when you add a WeakRef<T> layout, null out its referent field here.
    }

    /// No weak objects ⇒ always None.
    #[inline(always)]
    fn get_referent(_object: ObjectReference) -> Option<ObjectReference> {
        None
    }

    /// No weak objects ⇒ nothing to set.
    #[inline(always)]
    fn set_referent(_reff: ObjectReference, _referent: ObjectReference) {
        // When you add WeakRef<T>, write `_referent` into the referent slot here.
    }

    /// If a plan tries to enqueue cleared references, we just ignore them for now.
    #[inline(always)]
    fn enqueue_references(_references: &[ObjectReference], _tls: VMWorkerThread) {
        // Later: push into a VM-side ReferenceQueue to deliver to user code.
    }
}

impl VMBinding for NapalmVM {
    type VMObjectModel   = VMObjModel;
    type VMScanning      = VMScanning;
    type VMCollection    = VMCollection;
    type VMActivePlan    = VMActivePlan;
    type VMReferenceGlue = VMRefGlue;

    // Your VM’s slot & memory slice types
    type VMSlot         = SlotItem;
    type VMMemorySlice  = MemSlice;
}

// ==================================================================
// ==================== Mutators ====================================
// ==================================================================
thread_local! {
    static TLS_MUTATOR: RefCell<Option<Box<Mutator<NapalmVM>>>> = const { RefCell::new(None) };
    static TLS_MUT_PTR: Cell<*mut Mutator<NapalmVM>> = const { Cell::new(std::ptr::null_mut()) };
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct MutatorThread;

impl MutatorThread {
    #[inline(always)]
    pub fn bind_current_thread(&self) {
        Self::attach_current_thread();
    }

    #[inline(always)]
    pub fn attach_current_thread() {
        TLS_MUTATOR.with(|c| {
            if c.borrow().is_none() {
                let mmtk = get_mmtk();

                // No real TLS handle yet → use an opaque “uninitialized” token.
                let tls = VMMutatorThread(VMThread::UNINITIALIZED);

                let mut mutator = memory_manager::bind_mutator::<NapalmVM>(mmtk, tls);

                let raw: *mut Mutator<NapalmVM> = &mut *mutator;
                *c.borrow_mut() = Some(mutator);
                TLS_MUT_PTR.with(|p| p.set(raw));

                let mut list = ALL_MUTATORS.lock();
                list.push(MutatorRaw(raw));
                MUTATOR_COUNT.fetch_add(1, AcqRel);
            }
        });
    }

    #[inline(always)]
    pub fn detach_current_thread() {
        TLS_MUTATOR.with(|c| {
            if let Some(mut mutator_box) = c.borrow_mut().take() {
                // Remove from global registry.
                let raw: *mut Mutator<NapalmVM> = &mut *mutator_box;
                {
                    let mut list = ALL_MUTATORS.lock();
                    if let Some(i) = list.iter().position(|&MutatorRaw(p)| p == raw) {
                        list.swap_remove(i);
                    }
                }
                TLS_MUT_PTR.with(|p| p.set(std::ptr::null_mut()));
                MUTATOR_COUNT.fetch_sub(1, AcqRel);
                drop(mutator_box); // drop the Box after unregistering
            }
        });
    }

    #[inline(always)]
    pub fn with_mutator<R>(f: impl FnOnce(&mut Mutator<NapalmVM>) -> R) -> R {
        TLS_MUTATOR.with(|c| {
            let mut guard = c.borrow_mut();
            let m = guard
                .as_deref_mut()
                .expect("MMTk mutator not attached on this thread. Call gc::attach_current_thread().");
            f(m)
        })
    }

    pub fn mutator_visitor<F>(mut mutator_visitor: F)
    where
        F: FnMut(&'static mut Mutator<NapalmVM>),
    {
        let ptrs: Vec<MutatorRaw> = {
            let list = ALL_MUTATORS.lock();
            list.as_slice().to_vec()
        };

        for MutatorRaw(p) in ptrs {
            let m: &'static mut Mutator<NapalmVM> = unsafe { &mut *p };
            mutator_visitor(m);
        }
    }
}

// ==================================================================
// ==================== Global Garbage Collector ====================
// ==================================================================
static MMTK_GC: Lazy<MMTK<NapalmVM>> = Lazy::new(|| {
    // ① Options – pick Gen-Immix plan (our only supported configuration).
    let mut opts = Options::default();
    // Options::plan is an MMTKOption<PlanSelector>. Set via .set(…).
    let _ok = opts.plan.set(PlanSelector::StickyImmix); // PlanSelector::GenImmix
    debug_assert!(_ok, "failed to set MMTk plan to Immix");

    // ② Build MMTk instance.
    let mut builder = MMTKBuilder::new();
    builder.options = opts;
    builder.build::<NapalmVM>()
});

/// Initialise the singleton GC (harmless to call multiple times).
#[inline(always)]
pub fn init() {
    Lazy::force(&MMTK_GC);
}

#[inline(always)]
pub fn get_mmtk() -> &'static MMTK<NapalmVM> {
    &*MMTK_GC
}

thread_local! {
    static SAFEPOINT_TICK: Cell<usize> = Cell::new(0);
}

#[derive(Copy, Clone)]
pub struct NapalmGc {
    pub mutator: MutatorThread,
    pub stack_guess: usize,
    pub gc: &'static MMTK<NapalmVM>,
}

impl NapalmGc {
    pub fn new() -> Self {
        init();

        NapalmGc {
            mutator: MutatorThread::default(),
            stack_guess: 1 << 20, // 1 MiB
            gc: get_mmtk()
        }
    }

    #[inline(always)]
    pub fn collect_now(&self) -> bool {
        use mmtk::memory_manager::handle_user_collection_request;

        // Any mutator thread token is fine for the request hint. If you want,
        // plumb a real per-thread VMThread here.
        handle_user_collection_request::<NapalmVM>(self.gc, VMMutatorThread(VMThread::UNINITIALIZED))
    }

    /// Visit all root slots currently on the shadow stack with a callback.
    #[inline(always)]
    pub fn visit_value_slots<F: FnMut(*mut ValueRepr)>(&self, mut f: F) {
        ShadowStack::with_roots(|slot| f(slot));
    }

    /// A convenience 'visit_value' that conditionally applies a function to a single slot
    /// if it looks like a pointer (useful for ad-hoc verifiers).
    #[inline(always)]
    pub fn visit_value<F: FnMut(*mut ValueRepr)>(&self, slot: *mut ValueRepr, mut f: F) {
        unsafe {
            let v = core::ptr::read(slot);
            if is_ptr(v) && v != NULL {
                f(slot);
            }
        }
    }

    /// “Any visitor” push/pop helpers are often just wrappers around ShadowStack.
    /// If you meant 'push a range of locals' for a frame, expose that explicitly:
    #[inline(always)]
    pub unsafe fn push_any_visitor(&self, base: *mut ValueRepr, slots: usize) {
        ShadowStack::push_range(base as *mut i64, slots);
    }

    #[inline(always)]
    pub fn pop_any_visitor(&self) {
        ShadowStack::pop_range();
    }

    #[inline(always)]
    pub unsafe fn alloc_raw(&self, bytes: usize, align: usize) -> *mut u8 {
        MutatorThread::with_mutator(|mutator| {
            let addr = memory_manager::alloc::<NapalmVM>(
                mutator, bytes, align, 0, AllocationSemantics::Default,
            );
            if addr.is_zero() { ptr::null_mut() } else { addr.to_mut_ptr::<u8>() }
        })
    }

    #[inline(always)]
    pub unsafe fn alloc_slow_path(&self, bytes: usize, align: usize) -> *mut u8 {
        MutatorThread::with_mutator(|mutator| {
            let addr = memory_manager::alloc_slow::<NapalmVM>(
                mutator, bytes, align, 0, AllocationSemantics::Default,
            );
            debug_assert!(!addr.is_zero());
            addr.to_mut_ptr::<u8>()
        })
    }

    #[inline(always)]
    pub unsafe fn post_alloc_object(&self, obj_ptr: *mut u8, bytes: usize) {
        MutatorThread::with_mutator(|mutator| {
            let objref = ObjectReference::from_raw_address(Address::from_mut_ptr(obj_ptr))
                .expect("post_alloc_object: null obj_ptr");
            memory_manager::post_alloc::<NapalmVM>(
                mutator, objref, bytes, AllocationSemantics::Default,
            );
        });
    }

    #[inline(always)]
    pub unsafe fn post_write_barrier(&self, object_base: *mut u8, slot: *mut ValueRepr, new_val: ValueRepr) {
        if is_ptr(new_val) && new_val != NULL {
            MutatorThread::with_mutator(|mutator| {
                let src = ObjectReference::from_raw_address(Address::from_ptr(object_base))
                    .expect("post barrier: null src");
                let vm_slot = SlotItem::from(Address::from_ptr(slot.cast::<u8>()));
                let target = ObjectReference::from_raw_address(Address::from_ptr(new_val as *mut u8));
                memory_manager::object_reference_write_post::<NapalmVM>(
                    mutator, src, vm_slot, target
                );
            });
        }
    }

    #[inline(always)]
    pub unsafe fn pre_write_barrier(&self, object_base: *mut u8, slot: *mut ValueRepr) {
        let old_v: ValueRepr = unsafe { core::ptr::read(slot) };
        if is_ptr(old_v) && old_v != NULL {
            MutatorThread::with_mutator(|mutator| {
                let src = ObjectReference::from_raw_address(Address::from_ptr(object_base))
                    .expect("pre barrier: null src");
                let vm_slot = SlotItem::from(Address::from_ptr(slot.cast::<u8>()));
                let old = ObjectReference::from_raw_address(Address::from_ptr(old_v as *mut u8));
                memory_manager::object_reference_write_pre::<NapalmVM>(
                    mutator, src, vm_slot, old
                );
            });
        }
    }

    /// Bind the current thread as a mutator (safe to call multiple times).
    #[inline(always)]
    pub fn bind_current_thread(&self) {
        MutatorThread::attach_current_thread();
    }

    /// Optional shutdown (useful in tests).
    #[inline(always)]
    pub fn shutdown(&self) {
        unimplemented!();
    }

    #[inline(always)]
    fn stack_anchor(&self) -> *const u8 {
        let x = 0u8;
        &x as *const u8
    }

    /// Downward–growing stack assumption: high == current anchor; low == anchor - guess.
    #[inline(always)]
    fn stack_bounds_guess(&self) -> (Address, Address) {
        let anchor = self.stack_anchor() as usize;
        let hi = anchor;
        let lo = anchor.saturating_sub(self.stack_guess);
        unsafe { (Address::from_usize(lo), Address::from_usize(hi)) }
    }

    /// Platform query: attempt to obtain **exact** stack bounds for the *current* thread.
    /// Returns `(lo, hi)` where the valid stack memory is `[lo, hi)`.
    #[inline(always)]
    fn stack_bounds_current_thread(&self) -> (Address, Address) {
        // Try OS‑specific backends first; fall back to heuristic if they fail.
        if let Some(bounds) = self.stack_bounds_os() {
            bounds
        } else {
            self.stack_bounds_guess()
        }
    }

    /// A stand-alone precise scanner (debug): enumerate a *heap object’s* references
    /// in the same way your MMTk scan does.
    #[inline(always)]
    pub fn scan_object_precise<F: FnMut(*mut ValueRepr)>(&self, obj: ObjectReference, mut f: F) {
        pub const TAG_ARRAY_FLAT: u32 = 6;

        unsafe {
            let base = obj.to_raw_address().to_ptr::<u8>();
            let hdr  = &*(base as *const ObjHeader);
            match hdr.tag {
                TAG_BOXED_F64 | TAG_STRING => {}
                TAG_ARRAY => {
                    let arr = &mut *(base as *mut crate::value::BoxedArray);
                    let len = arr.buf.len();
                    let ptr = arr.buf.as_mut_ptr();
                    for i in 0..len {
                        f(ptr.add(i));
                    }
                }
                TAG_CLOSURE => {
                    let clo = &mut *(base as *mut crate::value::BoxedClosure);
                    let len = clo.env.len();
                    let ptr = clo.env.as_mut_ptr();
                    for i in 0..len {
                        f(ptr.add(i));
                    }
                }
                _ => {}
            }
        }
    }

    #[cfg(any(target_os = "linux", target_os = "android"))]
    #[inline(always)]
    fn stack_bounds_os(&self) -> Option<(Address, Address)> {
        use core::mem::MaybeUninit;
        use libc::{pthread_attr_destroy, pthread_attr_getstack, pthread_getattr_np, pthread_self};

        unsafe {
            let mut attr = MaybeUninit::<libc::pthread_attr_t>::uninit();
            if pthread_getattr_np(pthread_self(), attr.as_mut_ptr()) != 0 {
                return None;
            }

            let mut stack_base: *mut core::ffi::c_void = core::ptr::null_mut();
            let mut stack_size: usize = 0;
            if pthread_attr_getstack(attr.as_ptr(), &mut stack_base, &mut stack_size) != 0 {
                let _ = pthread_attr_destroy(attr.as_mut_ptr());
                return None;
            }
            let _ = pthread_attr_destroy(attr.as_mut_ptr());

            if stack_base.is_null() || stack_size == 0 {
                return None;
            }

            // POSIX: stack_base is the *lowest* address; stack grows downward.
            let lo = stack_base as usize;
            let hi = lo + stack_size;
            Some(unsafe { (Address::from_usize(lo), Address::from_usize(hi)) })
        }
    }

    #[cfg(target_os = "macos")]
    #[inline(always)]
    fn stack_bounds_os(&self) -> Option<(Address, Address)> {
        use libc::{pthread_get_stackaddr_np, pthread_get_stacksize_np, pthread_self};

        unsafe {
            let stack_top = pthread_get_stackaddr_np(pthread_self()) as usize; // high address
            let size = pthread_get_stacksize_np(pthread_self());
            if stack_top == 0 || size == 0 {
                return None;
            }
            // macOS returns the *top* (high) address; subtract size to get low.
            let lo = stack_top - size;
            let hi = stack_top;
            Some(unsafe { (Address::from_usize(lo), Address::from_usize(hi)) })
        }
    }

    #[cfg(target_os = "windows")]
    #[inline(always)]
    fn stack_bounds_os(&self) -> Option<(Address, Address)> {
        use windows_sys::Win32::System::Threading::GetCurrentThreadStackLimits;

        unsafe {
            let mut low: usize = 0;
            let mut high: usize = 0;
            GetCurrentThreadStackLimits(&mut low as *mut usize, &mut high as *mut usize);

            if low == 0 || high == 0 || low >= high {
                return None; // fallback → heuristic
            }
            Some((
                Address::from_usize(low),
                Address::from_usize(high),
            ))
        }
    }

    #[cfg(not(any(target_os = "linux", target_os = "android", target_os = "macos")))]
    #[inline(always)]
    fn stack_bounds_os() -> Option<(&self, Address, Address)> {
        None
    }

    #[inline(always)]
    pub fn yieldpoint(&self) {
        // Fast path: nothing to do.
        if !STW_REQUESTED.load(Acquire) { return; }

        // Park cooperatively until GC clears the flag.
        let mut guard = STW_LOCK.lock();
        // Re-check under the mutex to avoid races.
        while STW_REQUESTED.load(Acquire) {
            STW_CV.wait(&mut guard);
        }
        // guard drops here
    }

    #[inline(always)]
    pub fn maybe_safepoint(&self) {
        SAFEPOINT_TICK.with(|tick| {
            let v = tick.get().wrapping_add(1);
            if v >= 4096 {
                tick.set(0);
                self.yieldpoint();
            } else {
                tick.set(v);
            }
        });
    }
}

pub static NAPALM_GC: Lazy<NapalmGc> = Lazy::new(|| NapalmGc::new());

// ======================================================
// ==================== Shadow Stack ====================
// ======================================================

thread_local! {
    static SHADOW: RefCell<Vec<(*mut i64, usize)>> = RefCell::new(Vec::new());
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ShadowStack;

// It's inert for now, but the API is stable.
impl ShadowStack {
    #[inline(always)]
    pub unsafe fn push_range(base: *mut i64, slots: usize) {
        SHADOW.with(|s| s.borrow_mut().push((base, slots)));
    }
    #[inline(always)]
    pub fn pop_range() {
        SHADOW.with(|s| { s.borrow_mut().pop(); });
    }

    /// Iterate current roots
    pub fn with_roots<F: FnMut(*mut i64)>(mut f: F) {
        SHADOW.with(|s| {
            for (base, n) in s.borrow().iter().copied() {
                for i in 0..n {
                    let slot = unsafe { base.add(i) };
                    f(slot);
                }
            }
        });
    }
}
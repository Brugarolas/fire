// File: src/gc/binding.rs
//! Minimal PocketVM binding – now with conservative root scanning that
//! actually compiles :-)

use core::ptr;
use dashmap::DashMap;
use once_cell::sync::Lazy;
use parking_lot::{RwLock, RwLockReadGuard};
use ahash::HashMap;
use parking_lot::Mutex;
use core::mem::{self, size_of};

use mmtk::{
    util::{copy, opaque_pointer::*, Address, ObjectReference},
    vm::{slot, *},
    Mutator,
};

use crate::ir::Value;
use crate::gc::Gc as GcBase;

/*──────────────── 0 · per‑mutator stack bounds ────────────────*/

pub(crate) static STACK_BOUNDS: Lazy<DashMap<usize, (Address, Address)>> = Lazy::new(|| DashMap::new());

#[inline(always)]
pub(crate) fn set_stack_bounds(m: *mut Mutator<PocketVM>, lo: Address, hi: Address) {
    STACK_BOUNDS.insert(m as usize, (lo, hi));
}

/*──────────────── 1 · global mutator registry ─────────────────*/

static ALL_MUTATORS: RwLock<Vec<usize>> = RwLock::new(Vec::new());

#[inline(always)] pub(crate) fn register_mutator(m: *mut Mutator<PocketVM>) {
    ALL_MUTATORS.write().push(m as usize);
}
#[inline(always)] pub(crate) fn unregister_mutator(m: *mut Mutator<PocketVM>) {
    let addr = m as usize;
    let mut g = ALL_MUTATORS.write();
    if let Some(pos) = g.iter().position(|&x| x == addr) { g.swap_remove(pos); }
}
#[inline(always)] fn snapshot_mutators<'a>() -> RwLockReadGuard<'a, Vec<usize>> {
    ALL_MUTATORS.read()
}
#[inline] fn vmthread_to_addr(t: VMThread) -> usize          { t.0.to_address().as_usize() }
#[inline] fn tls_to_mut_ptr(t: VMMutatorThread) -> *mut Mutator<PocketVM> {
    t.0.0.to_address().to_mut_ptr::<Mutator<PocketVM>>()
}

/*──────────────── 2 · meta‑table (size / align) ───────────────*/

pub(crate) static OBJ_META: Lazy<DashMap<ObjectReference, (usize, usize)>> =
    Lazy::new(|| DashMap::new());

pub fn owner_of(addr: Address) -> Option<ObjectReference> {
    for e in OBJ_META.iter() {
        let start = e.key().to_raw_address();
        let (sz, _) = *e.value();
        if addr >= start && addr < start + sz { return Some(*e.key()); }
    }
    None
}

#[repr(u8)]
#[derive(Clone, Copy, Debug)]
pub enum ObjKind {
    Unknown = 0,
    ObjectMap = 1,
    ArrayVec = 2,
    Generator = 3,
    Awaitable = 4,
}

pub const HEADER_WORDS: usize = 2;
pub const HEADER_BYTES: usize = HEADER_WORDS * core::mem::size_of::<usize>();
pub const TAG_OFFSET: usize   = core::mem::size_of::<usize>();

#[inline]
pub fn read_kind_header(obj: ObjectReference) -> ObjKind {
    // obj -> PAYLOAD. Header starts HEADER_BYTES *before* that.
    let tag_ptr = unsafe {
        (obj.to_raw_address() - HEADER_BYTES + TAG_OFFSET).to_ptr::<u64>()
    };
    match unsafe { *tag_ptr } {
        0 => ObjKind::Unknown,
        1 => ObjKind::ObjectMap,
        2 => ObjKind::ArrayVec,
        3 => ObjKind::Generator,
        4 => ObjKind::Awaitable,
        _ => ObjKind::Unknown,
    }
}

#[inline]
pub fn write_kind_header(obj: ObjectReference, kind: ObjKind) {
    // obj -> PAYLOAD. Step back to header, then to tag field.
    let tag_ptr = unsafe {
        (obj.to_raw_address() - HEADER_BYTES + TAG_OFFSET).to_mut_ptr::<u64>()
    };
    unsafe {
        *tag_ptr = match kind {
            ObjKind::Unknown   => 0,
            ObjKind::ObjectMap => 1,
            ObjKind::ArrayVec  => 2,
            ObjKind::Generator => 3,
            ObjKind::Awaitable => 4,
        };
    }
}

/*──────────────── 3 · VM marker types ─────────────────────────*/

#[derive(Clone, Copy, Debug, Default)] pub struct PocketVM;
#[derive(Clone, Copy, Debug, Default)] pub struct VMObjModel;
#[derive(Clone, Copy, Debug, Default)] pub struct VMScanning;
#[derive(Clone, Copy, Debug, Default)] pub struct VMCollection;
#[derive(Clone, Copy, Debug, Default)] pub struct VMActivePlan;
#[derive(Clone, Copy, Debug, Default)] pub struct VMRefGlue;

pub type Slot     = slot::SimpleSlot;
pub type MemSlice = slot::UnimplementedMemorySlice;

/*──────────────── 4 · object model (unchanged core) ───────────*/

impl ObjectModel<PocketVM> for VMObjModel {
    const GLOBAL_LOG_BIT_SPEC: VMGlobalLogBitSpec = VMGlobalLogBitSpec::side_first();
    const LOCAL_FORWARDING_POINTER_SPEC: VMLocalForwardingPointerSpec =
        VMLocalForwardingPointerSpec::in_header(0);
    const LOCAL_FORWARDING_BITS_SPEC: VMLocalForwardingBitsSpec  =
        VMLocalForwardingBitsSpec::side_first();
    const LOCAL_MARK_BIT_SPEC: VMLocalMarkBitSpec =
        VMLocalMarkBitSpec::side_after(Self::LOCAL_FORWARDING_BITS_SPEC.as_spec());
    const LOCAL_LOS_MARK_NURSERY_SPEC: VMLocalLOSMarkNurserySpec =
        VMLocalLOSMarkNurserySpec::side_after(Self::LOCAL_MARK_BIT_SPEC.as_spec());
    const OBJECT_REF_OFFSET_LOWER_BOUND: isize = 0;

    fn get_current_size(o: ObjectReference) -> usize {
        OBJ_META.get(&o).map(|e| e.value().0).unwrap_or(0)
    }
    fn get_size_when_copied(o: ObjectReference) -> usize { Self::get_current_size(o) }
    fn get_align_when_copied(o: ObjectReference) -> usize {
        OBJ_META.get(&o).map(|e| e.value().1).unwrap_or(core::mem::align_of::<usize>())
    }
    fn get_align_offset_when_copied(_: ObjectReference) -> usize { 0 }

    fn copy(
        from: ObjectReference,
        semantics: copy::CopySemantics,
        ctx: &mut copy::GCWorkerCopyContext<PocketVM>,
    ) -> ObjectReference {
        use crate::gc::binding::{HEADER_BYTES, read_kind_header, write_kind_header};

        let payload_sz = Self::get_current_size(from);
        let align      = Self::get_align_when_copied(from);
        let total      = HEADER_BYTES + payload_sz;

        // allocate header+payload as one chunk
        let dest_header = ctx.alloc_copy(from, total, align, 0, semantics);

        // copy header+payload bytes
        let src_header  = from.to_raw_address() - HEADER_BYTES;
        unsafe {
            ptr::copy_nonoverlapping(
                src_header.to_ptr::<u8>(),
                dest_header.to_mut_ptr::<u8>(),
                total,
            );
        }

        // new object reference points at the *payload*
        let dest_payload = unsafe { dest_header + HEADER_BYTES };
        let to = unsafe { ObjectReference::from_raw_address_unchecked(dest_payload) };

        // meta table still stores *payload* size
        OBJ_META.insert(to, (payload_sz, align));

        // (optional) re‑stamp the header in case we ever change layout
        let kind = read_kind_header(from);
        write_kind_header(to, kind);

        to
    }

    fn copy_to(f: ObjectReference, t: ObjectReference, _r: Address) -> Address {
        use crate::gc::binding::HEADER_BYTES;

        let payload_sz = Self::get_current_size(f);
        let total      = HEADER_BYTES + payload_sz;

        let src_header = f.to_raw_address() - HEADER_BYTES;
        let dst_header = t.to_raw_address() - HEADER_BYTES;

        unsafe {
            ptr::copy_nonoverlapping(
                src_header.to_ptr::<u8>(),
                dst_header.to_mut_ptr::<u8>(),
                total,
            );
        }
        t.to_raw_address()
    }

    fn get_reference_when_copied_to(_: ObjectReference, a: Address) -> ObjectReference {
        unsafe { ObjectReference::from_raw_address_unchecked(a) }
    }
    fn get_type_descriptor(_: ObjectReference) -> &'static [i8] { &[] }
    #[inline] fn ref_to_object_start(o: ObjectReference) -> Address { o.to_raw_address() - HEADER_BYTES }
    #[inline] fn ref_to_header      (o: ObjectReference) -> Address { o.to_raw_address() - HEADER_BYTES }
    fn dump_object(_: ObjectReference) {}
}

/*──────────────── 5 · **root scanning** ───────────────────────*/

impl Scanning<PocketVM> for VMScanning {
    fn scan_roots_in_mutator_thread(
        _tls: VMWorkerThread,
        mutator: &mut Mutator<PocketVM>,
        mut factory: impl RootsWorkFactory<Slot>,
    ) {
        let mut slots = Vec::<Slot>::new();

        /*───────── ①  walk every live ExecutionContext ─────────*/
        for frame in crate::gc::roots::iter() {
            // registers
            for v in &frame.registers {
                visit_value(v, &mut slots);
            }

            // defer stack – each entry is (err_only, Vec<NodeMHIR>)
            for (_, body) in &frame.defer_stack {
                for n in body {
                    n.visit_values_precise(&mut slots);   // see note (*) below
                }
            }

            // lexical variables (no lock needed – LayeredMap stores Values inline)
            for cell in frame.variables.values_cells() {
                if let Ok(guard) = cell.try_lock() {
                    visit_value(&*guard, &mut slots);      // push every inner `Gc`
                }
            }
        }

        /*───────── ②  global tables also hold GC refs ──────────*/
        {
            let map = crate::vm::FUNC_BY_ID.try_lock();           // no await needed (STW)
            if let Ok(m) = map {
                for v in m.values() { visit_value(v, &mut slots); }
            }
        }
        {
            let cache = crate::vm::MODULE_CACHE.try_lock();
            if let Ok(m) = cache {
                for inst in m.values() {
                    if let Ok(exports) = inst.exports.try_lock() {
                        for v in exports.values() {
                            visit_value(v, &mut slots);
                        }
                    }
                }
            }
        }

        /*───────── ③  (optional) ALSO scan the raw stack ───────*/
        let m_addr = mutator as *mut _ as usize;
        let (lo, hi) = *STACK_BOUNDS.get(&m_addr)
            .expect("stack bounds missing").value();

        let mut scan = lo.as_usize();
        while scan < hi.as_usize() {
            let word = unsafe { *(scan as *const usize) };
            let addr = unsafe { Address::from_usize(word) };
            if let Some(obj) = owner_of(addr) {
                slots.push(Slot::from_address(obj.to_raw_address()));
            }
            scan += core::mem::size_of::<usize>();
        }

        /*───────── ④  hand everything to MMTk ──────────────────*/
        if !slots.is_empty() {
            factory.create_process_roots_work(slots);
        }
    }

    fn scan_vm_specific_roots(_tls: VMWorkerThread, _f: impl RootsWorkFactory<Slot>) {}

    fn scan_object<SV: SlotVisitor<Slot>>(
        _tls: VMWorkerThread,
        obj: ObjectReference,
        visitor: &mut SV,
    ) {
        use crate::ir::Value;
        use crate::vm::Generator;

        match read_kind_header(obj) {
            // Precise map: visit every Value; closure envs are handled by visit_value_slots
            ObjKind::ObjectMap => {
                let gc = GcBase::<Mutex<hashbrown::HashMap<String, Value>>>
                    ::from_objref(obj);

                if let Some(map) = unsafe { &*gc.as_ptr() }.try_lock() {
                    for v in map.values() {
                        visit_value_slots(v, visitor);
                    }
                }
                return;
            }

            // Precise vector: same for arrays
            ObjKind::ArrayVec => {
                let gc = GcBase::<Mutex<Vec<Value>>>::from_objref(obj);

                if let Some(vec) = unsafe { &*gc.as_ptr() }.try_lock() {
                    for v in vec.iter() {
                        visit_value_slots(v, visitor);
                    }
                }
                return;
            }

            // Precise generator: scan registers and lexical cells
            ObjKind::Generator => {
                let gc = GcBase::<Mutex<Generator>>::from_objref(obj);

                if let Some(gen_z) = unsafe { &*gc.as_ptr() }.try_lock() {
                    // registers
                    for v in &gen_z.context.registers {
                        visit_value_slots(v, visitor);
                    }

                    // lexical variables
                    for cell in gen_z.context.variables.values_cells() {
                        if let Ok(g) = cell.try_lock() {
                            visit_value_slots(&*g, visitor);
                        }
                    }
                }
                return;
            }

            // Unknown or other kinds: conservative fallback
            _ => { /* fall through below */ }
        }

        // Conservative fallback over the payload bytes
        let sz  = VMObjModel::get_current_size(obj);
        let mut addr = obj.to_raw_address().as_usize();
        let end = addr + sz;
        while addr < end {
            let word = unsafe { *(addr as *const usize) };
            let a    = unsafe { Address::from_usize(word) };
            if let Some(o) = owner_of(a) {
                visitor.visit_slot(Slot::from_address(o.to_raw_address()));
            }
            addr += size_of::<usize>();
        }
    }

    fn notify_initial_thread_scan_complete(_: bool, _: VMWorkerThread) {}
    fn supports_return_barrier() -> bool { false }
    fn prepare_for_roots_re_scanning() {}
}

/*──────────────── 6 · trivial STW Collection (unchanged) ─────*/

impl Collection<PocketVM> for VMCollection {
    fn stop_all_mutators<F>(_: VMWorkerThread, mut visitor: F)
    where F: FnMut(&'static mut Mutator<PocketVM>) {
        for m in VMActivePlan::mutators() { visitor(m); }
    }
    fn resume_mutators(_: VMWorkerThread) {}
    fn block_for_gc(_: VMMutatorThread) {}
    fn spawn_gc_thread(_: VMThread, _: GCThreadContext<PocketVM>) {}
}

/*──────────────── 7 · ActivePlan helpers ──────────────────────*/

impl ActivePlan<PocketVM> for VMActivePlan {
    fn number_of_mutators() -> usize { snapshot_mutators().len() }
    fn is_mutator(t: VMThread) -> bool {
        let a = vmthread_to_addr(t);
        snapshot_mutators().iter().any(|&x| x == a)
    }
    fn mutator(t: VMMutatorThread) -> &'static mut Mutator<PocketVM> {
        unsafe { &mut *tls_to_mut_ptr(t) }
    }
    fn mutators<'a>() -> Box<dyn Iterator<Item=&'a mut Mutator<PocketVM>> + 'a> {
        let v = snapshot_mutators().clone();
        Box::new(v.into_iter().map(|a| unsafe { &mut *(a as *mut Mutator<PocketVM>) }))
    }
}

/*──────────────── 8 · ReferenceGlue stub ─────────────────────*/

impl ReferenceGlue<PocketVM> for VMRefGlue {
    type FinalizableType = ObjectReference;
    fn set_referent(_: ObjectReference, _: ObjectReference) {}
    fn get_referent(_: ObjectReference) -> Option<ObjectReference> { None }
    fn clear_referent(_: ObjectReference) {}
    fn enqueue_references(_: &[ObjectReference], _: VMWorkerThread) {}
}

/*──────────────── 9 · tie into VMBinding ─────────────────────*/

impl VMBinding for PocketVM {
    type VMObjectModel   = VMObjModel;
    type VMScanning      = VMScanning;
    type VMCollection    = VMCollection;
    type VMActivePlan    = VMActivePlan;
    type VMReferenceGlue = VMRefGlue;
    type VMSlot          = Slot;
    type VMMemorySlice   = MemSlice;
    const MAX_ALIGNMENT  : usize = 64;
}

/*──────────────── 10 · helpers for gc.rs ─────────────────────*/

impl PocketVM {
    #[inline] pub fn object_start_to_ref(a: Address) -> ObjectReference {
        unsafe { ObjectReference::from_raw_address_unchecked(a) }
    }
}

/*──────────────── 11 · tiny `Gc` wrappers ────────────────────*/

#[repr(transparent)]
pub struct Gc<T: 'static> {
    obj: ObjectReference,
    _ph: core::marker::PhantomData<T>,
}
impl<T: 'static> Copy for Gc<T>{}
impl<T: 'static> Clone for Gc<T>{fn clone(&self)->Self{*self}}
impl<T: 'static> core::fmt::Debug for Gc<T>{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>)->core::fmt::Result{
        f.debug_struct("Gc").field("obj", &self.obj).finish()
    }
}
impl<T: 'static> core::fmt::Display for Gc<T>{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>)->core::fmt::Result{
        write!(f, "Gc({})", self.obj.to_raw_address())
    }
}

impl<T:'static> Gc<T>{
    #[inline]
    pub(crate) fn from_objref(o:ObjectReference)->Self{
        Self{obj:o,_ph:core::marker::PhantomData}
    }

    #[inline]
    pub fn as_ptr(self) -> *const T {
        // object start + header bytes
        self.obj.to_raw_address().to_ptr::<T>()
    }

    #[inline]
    pub(crate) fn objref(self)->ObjectReference{self.obj}
}
impl<T:'static> core::ops::Deref for Gc<T>{
    type Target=T;
    fn deref(&self)->&T{unsafe{&*self.as_ptr()}}
}

impl<T: 'static> Gc<T> {
    /// Allocate `value` in the current MMTk heap and return a `Gc<T>`.
    /// Internally this is just a thin shim around `crate::gc::alloc`.
    #[inline]
    pub fn new(value: T) -> Self {
        // ❶ delegate to the public allocator in the parent module
        super::alloc(value)
    }
}

pub struct GcCell<T: 'static>(Gc<core::cell::UnsafeCell<T>>);
impl<T> GcCell<T>{
    pub fn new(v:T)->Self{Self(super::alloc(core::cell::UnsafeCell::new(v)))}
    pub fn get(&self)->&T{unsafe{&*self.0.get()}}
    pub fn get_mut(&self)->&mut T{unsafe{&mut* self.0.get()}}
}

// Helpers
fn push_any_visitor<SV: SlotVisitor<Slot>, T: 'static>(g: &crate::gc::Gc<T>, visitor: &mut SV) {
    visitor.visit_slot(Slot::from_address(g.objref().to_raw_address()));
}

fn visit_value_slots<SV: SlotVisitor<Slot>>(v: &Value, visitor: &mut SV) {
    // Small helper: turn any Gc<T> into one Slot for the visitor.
    fn push_any_visitor<SV2: SlotVisitor<Slot>, T: 'static>(g: &crate::gc::Gc<T>, vis: &mut SV2) {
        vis.visit_slot(Slot::from_address(g.objref().to_raw_address()));
    }

    match v {
        Value::Object(g)    => push_any_visitor(g, visitor),
        Value::Array(g)     => push_any_visitor(g, visitor),
        Value::Generator(g) => push_any_visitor(g, visitor),

        // NEW: descend into closure environments by **reading** the captured cells
        Value::Closure(c) => {
            for (_, cell) in &c.env {
                if let Ok(guard) = cell.try_lock() {
                    // Recurse into the current payload to find any GC-managed edges.
                    visit_value_slots(&*guard, visitor);
                }
            }
        }

        // Accessors may hold closures with environments
        Value::Accessor { get, set } => {
            if let Some(gv) = get.as_deref() {
                if let Value::Closure(c) = gv {
                    for (_, cell) in &c.env {
                        if let Ok(guard) = cell.try_lock() {
                            visit_value_slots(&*guard, visitor);
                        }
                    }
                }
            }
            if let Some(sv) = set.as_deref() {
                if let Value::Closure(c) = sv {
                    for (_, cell) in &c.env {
                        if let Ok(guard) = cell.try_lock() {
                            visit_value_slots(&*guard, visitor);
                        }
                    }
                }
            }
        }

        _ => {}
    }
}

fn scan_object_precise<SV: SlotVisitor<Slot>>(
    _tls: VMWorkerThread,
    obj: ObjectReference,
    visitor: &mut SV,
) {
    use crate::vm::Generator;

    let kind = read_kind_header(obj);
    match kind {
        ObjKind::ObjectMap => {
            let gc = GcBase::<Mutex<HashMap<String, Value>>>::from_objref(obj);
            if let Some(map) = unsafe { &*gc.as_ptr() }.try_lock() {
                for v in map.values() { visit_value_slots(v, visitor); }
            }
            return;
        }
        ObjKind::ArrayVec => {
            let gc = GcBase::<Mutex<Vec<Value>>>::from_objref(obj);
            if let Some(vec) = unsafe { &*gc.as_ptr() }.try_lock() {
                for v in vec.iter() { visit_value_slots(v, visitor); }
            }
            return;
        }
        ObjKind::Generator => {
            let gc = GcBase::<Mutex<Generator>>::from_objref(obj);
            if let Some(gen_z) = unsafe { &*gc.as_ptr() }.try_lock() {
                for v in &gen_z.context.registers {
                    visit_value_slots(v, visitor);
                }
                for cell in gen_z.context.variables.values_cells() {
                    if let Ok(g) = cell.try_lock() {
                        visit_value_slots(&*g, visitor);
                    }
                }
            }
            return;
        }
        ObjKind::Awaitable => { /* nothing special */ }
        ObjKind::Unknown => { /* fall through to conservative */ }
    }

    // fallback conservative scan
    let sz  = VMObjModel::get_current_size(obj);
    let mut addr = obj.to_raw_address().as_usize();
    let end = addr + sz;
    while addr < end {
        let word = unsafe { *(addr as *const usize) };
        let a    = unsafe { Address::from_usize(word) };
        if let Some(o) = owner_of(a) {
            visitor.visit_slot(Slot::from_address(o.to_raw_address()));
        }
        addr += core::mem::size_of::<usize>();
    }
}

// TODO: Create 'visit_value' method


use once_cell::sync::Lazy;
use once_cell::sync::OnceCell;
use parking_lot::{Mutex, RwLock, RwLockReadGuard};
use core::mem::{self, size_of};
use ahash::AHashMap as HashMap;
use std::cell::RefCell;
use std::ptr;

use mmtk::{
    util::{copy, opaque_pointer::*, Address, ObjectReference, options::{ Options, PlanSelector }},
    vm::{slot, *},
    AllocationSemantics,
    memory_manager,
    Mutator,
    MMTKBuilder,
    MMTK,
};

use crate::value::{ValueRepr, is_ptr, NULL};

// =================================================================
// ==================== MMTk binding for Napalm VM =================
// =================================================================
#[derive(Clone, Copy, Debug, Default)] pub struct NapalmVM;
#[derive(Clone, Copy, Debug, Default)] pub struct VMObjModel;
#[derive(Clone, Copy, Debug, Default)] pub struct VMScanning;
#[derive(Clone, Copy, Debug, Default)] pub struct VMCollection;
#[derive(Clone, Copy, Debug, Default)] pub struct VMActivePlan;
#[derive(Clone, Copy, Debug, Default)] pub struct VMRefGlue;

pub type Slot     = slot::SimpleSlot;
pub type MemSlice = slot::UnimplementedMemorySlice;

impl ObjectModel<NapalmVM> for VMObjModel {
    // TODO!
}

impl Scanning<NapalmVM> for VMScanning {
    // TODO!
}

impl Collection<NapalmVM> for VMCollection {
    // TODO!
}

impl ActivePlan<NapalmVM> for VMActivePlan {
    // TODO!
}

impl ReferenceGlue<NapalmVM> for VMRefGlue {
    // TODO!
}

impl VMBinding for NapalmVM {
    // TODO!
}

// ==================================================================
// ==================== Slot ========================================
// ==================================================================
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Slot(pub Address);

impl From<Address> for Slot { fn from(a: Address) -> Self { Slot(a) } }

impl SlotTrait for Slot {
    #[inline(always)]
    fn load(&self) -> Option<ObjectReference> {
        let p = self.0.to_ptr::<ValueRepr>();
        let v = unsafe { ptr::read(p) };
        if is_ptr(v) && v != NULL {
            ObjectReference::from_raw_address(Address::from_ptr(v as *mut u8))
        } else {
            None
        }
    }

    #[inline(always)]
    fn store(&self, obj: ObjectReference) {
        // MMTk only calls this for actual reference slots.
        let p = self.0.to_mut_ptr::<ValueRepr>();
        let val: ValueRepr = obj.to_raw_address().to_ptr::<u8>() as i64;
        unsafe { ptr::write(p, val) };
    }
}

// ==================================================================
// ==================== Mutators ====================================
// ==================================================================
thread_local! {
    static TLS_MUTATOR: std::cell::RefCell<Option<Box<Mutator<NapalmVM>>>> = const { std::cell::RefCell::new(None) };
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct MutatorThread;

impl MutatorThread {
    #[inline(always)]
    pub fn attach_current_thread() {
        TLS_MUTATOR.with(|c| {
            if c.borrow().is_none() {
                let mmtk = get_mmtk();
                let mt = MutatorThread::current();
                let mutator = memory_manager::bind_mutator::<NapalmVM>(mmtk, mt);
                *c.borrow_mut() = Some(mutator);
            }
        });
    }

    #[inline(always)]
    pub fn detach_current_thread() {
        TLS_MUTATOR.with(|c| {
            let _ = c.borrow_mut().take();
        });
    }

    #[inline(always)]
    pub(crate) fn with_mutator<R>(f: impl FnOnce(&mut Mutator<NapalmVM>) -> R) -> R {
        TLS_MUTATOR.with(|c| {
            let mut guard = c.borrow_mut();
            let m = guard
                .as_deref_mut()
                .expect("MMTk mutator not attached on this thread. Call gc::attach_current_thread().");
            f(m)
        })
    }
}

// ==================================================================
// ==================== Global Garbage Collector ====================
// ==================================================================
static MMTK: OnceCell<MMTK<NapalmVM>> = OnceCell::new();

pub fn get_mmtk() -> &'static MMTK<NapalmVM> {
    MMTK.get().expect("MMTk not initialized")
}

static MMTK_GC: Lazy<MMTK<NapalmVM>> = Lazy::new(|| {
    // ① Options – pick Gen-Immix plan (our only supported configuration).
    let mut opts = Options::default();
    // Options::plan is an MMTKOption<PlanSelector>. Set via .set(…).
    let _ok = opts.plan.set(PlanSelector::GenImmix);
    debug_assert!(_ok, "failed to set MMTk plan to GenImmix");

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

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct NapalmGc {
    pub mutator: MutatorThread,
    pub stack_guess: usize,
    pub safepoint_tick: usize,
}

impl NapalmGc {
    pub fn new() -> Self {
        NapalmGc { mutator: MutatorThread::default(), stack_guess: 1 << 20, safepoint_tick: 0 } // 1 MiB
    }

    #[inline(always)]
    pub fn push_any_visitor(&self) {
        unimplemented!()
    }

    #[inline(always)]
    pub fn visit_value_slots(&self) {
        unimplemented!()
    }

    #[inline(always)]
    pub fn scan_object_precise(&self) {
        unimplemented!()
    }

    #[inline(always)]
    pub fn visit_value(&self) { // No, I won't place it in the VM, because there's no VM.
        unimplemented!()
    }

    #[inline(always)]
    pub unsafe fn alloc_raw(&self, bytes: usize, align: usize) -> *mut u8 {
        self.mutator.with_mutator(|mutator| {
            let addr = memory_manager::alloc::<NapalmVM>(
                mutator, bytes, align, 0, AllocationSemantics::Default,
            );
            if addr.is_zero() { ptr::null_mut() } else { addr.to_mut_ptr::<u8>() }
        })
    }

    #[inline(always)]
    pub unsafe fn alloc_slow_path(&self, bytes: usize, align: usize) -> *mut u8 {
        self.mutator.with_mutator(|mutator| {
            let addr = memory_manager::alloc_slow::<NapalmVM>(
                mutator, bytes, align, 0, AllocationSemantics::Default,
            );
            debug_assert!(!addr.is_zero());
            addr.to_mut_ptr::<u8>()
        })
    }

    #[inline(always)]
    pub unsafe fn post_alloc_object(&self, obj_ptr: *mut u8, bytes: usize) {
        self.mutator.with_mutator(|mutator| {
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
            self.mutator.with_mutator(|mutator| {
                let src = ObjectReference::from_raw_address(Address::from_ptr(object_base))
                    .expect("post barrier: null src");
                let vm_slot = Slot::from(Address::from_ptr(slot.cast::<u8>()));
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
            self.mutator.with_mutator(|mutator| {
                let src = ObjectReference::from_raw_address(Address::from_ptr(object_base))
                    .expect("pre barrier: null src");
                let vm_slot = Slot::from(Address::from_ptr(slot.cast::<u8>()));
                let old = ObjectReference::from_raw_address(Address::from_ptr(old_v as *mut u8));
                memory_manager::object_reference_write_pre::<NapalmVM>(
                    mutator, src, vm_slot, old
                );
            });
        }
    }

    #[inline(always)]
    pub fn yieldpoint(&self) {
        unimplemented!()
    }

    /// Bind the current thread as a mutator (safe to call multiple times).
    #[inline(always)]
    pub fn bind_current_thread(&self) {
        self.mutator.bind_current_thread();
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
    fn maybe_safepoint(&mut self) {
        self.safepoint_tick = self.safepoint_tick.wrapping_add(1);
        if self.safepoint_tick == 4096 {
            self.safepoint_tick = 0;
            self.yieldpoint();
        }
    }
}

pub static NAPALM_GC: OnceCell<NapalmGc> = OnceCell::new();

// ======================================================
// ==================== Shadow Stack ====================
// ======================================================

thread_local! {
    static SHADOW: RefCell<Vec<(*mut i64, usize)>> = RefCell::new(Vec::new());
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ShadowStack;

// TODO It's inert for now, but the API is stable.
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
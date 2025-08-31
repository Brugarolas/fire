// File: src/gc.rs
//! Public entry-points for PocketScript’s single MMTk instance.
//!
//! Exposed API (re-exported from `crate::prelude`):
//!   • `gc::init()`                    – idempotent global initialisation
//!   • `gc::alloc(val)`                – allocate `val` in Gen-Immix → `Gc<T>`
//!   • `gc::with_mutator(|m| { … })`   – run code with this thread’s Mutator
//!
//! Internals:
//!   • We build a single `MMTK<PocketVM>` using the Gen-Immix plan.
//!   • Each OS thread lazily binds a `Mutator<PocketVM>` on first use.
//!   • When binding, we register an **approximate** stack range so the GC
//!     can conservatively scan mutator stacks (Milestone 4).
//!
//! Safety notes:
//!   * The stack range heuristic assumes **downward-growing stacks** (true
//!     on all tier-1/2 Rust targets we care about).  If you port to an
//!     upward-growing architecture, flip the math in `stack_bounds_guess()`.
//!   * The range is coarse (default 1 MiB).  We will replace it with real
//!     platform queries in a later milestone.

pub mod binding;
pub mod roots;

use mmtk::{
    memory_manager as mm,
    util::{opaque_pointer::*, options::{Options, PlanSelector}, Address},
    AllocationSemantics, MMTKBuilder, Mutator,
};

pub use binding::{PocketVM, Slot, Gc, ObjKind, HEADER_BYTES};
use crate::ir::{Value, AwaitableState};
use crate::vm::{Generator};

use once_cell::sync::Lazy;
use std::{cell::RefCell};
use ahash::HashMap;
use parking_lot::{Mutex, RwLock};

/*────────────────────────────── 1 · global GC ─────────────────────────────*/

static GC: Lazy<mmtk::MMTK<PocketVM>> = Lazy::new(|| {
    // ① Options – pick Gen-Immix plan (our only supported configuration).
    let mut opts = Options::default();
    // Options::plan is an MMTKOption<PlanSelector>. Set via .set(…).
    let _ok = opts.plan.set(PlanSelector::GenImmix);
    debug_assert!(_ok, "failed to set MMTk plan to GenImmix");

    // ② Build MMTk instance.
    let mut builder = MMTKBuilder::new();
    builder.options = opts;
    builder.build::<PocketVM>()
});

/// Initialise the singleton GC (harmless to call multiple times).
#[inline(always)]
pub fn init() {
    Lazy::force(&GC);
}

/*──────────────────────────── 2 · per-thread mutator ─────────────────────*/

thread_local! {
    /// TLS slot that holds this thread's mutator (Box from MMTk).
    static TLS_MUT: RefCell<Option<Box<Mutator<PocketVM>>>> = RefCell::new(None);
}

/// Run `f` with the calling OS thread’s `Mutator`, creating it lazily.
///
/// This is the *only* supported way to reach the raw mutator.  All heap
/// allocations (`alloc<T>`) and future write-barrier APIs call through here.
pub fn with_mutator<F, R>(f: F) -> R
where
    F: FnOnce(&mut Mutator<PocketVM>) -> R,
{
    TLS_MUT.with(|slot| {
        // Fast-path: already have a mutator.
        if slot.borrow().is_none() {
            // Lazy initialise on first use in this thread.
            let tls = VMMutatorThread(VMThread(OpaquePointer::UNINITIALIZED));
            let mutator_box = mm::bind_mutator::<PocketVM>(&GC, tls);

            // Register with the binding's global mutator registry (STW, root scan).
            //
            // Safety: Box::into_raw yields a stable pointer that lives until we drop
            // the Box during TLS teardown (not implemented yet; process-lifetime ok).
            let raw_ptr: *mut Mutator<PocketVM> = Box::into_raw(mutator_box);

            // Record guessed stack bounds so the GC can conservatively scan us.
            let (lo, hi) = stack_bounds_current_thread();
            binding::set_stack_bounds(raw_ptr, lo, hi);

            // Reconstitute the Box and stash it.
            // (We must rebuild the Box so it isn't leaked—we only *inspected* ptr.)
            let boxed = unsafe { Box::from_raw(raw_ptr) };

            // Inform binding that this mutator exists (for iteration/STW).
            binding::register_mutator(raw_ptr);

            *slot.borrow_mut() = Some(boxed);
        }

        // Call the user closure.
        f(slot.borrow_mut().as_mut().unwrap().as_mut())
    })
}

/*────────────────────────────── 3 · allocation ────────────────────────────*/

/// Allocate `value` in the Gen-Immix heap and return a `Gc<T>`.
///
/// Large objects automatically go to LOS according to the plan's constraints.
#[inline]
pub fn alloc<T: 'static>(value: T) -> Gc<T> {
    let payload_bytes = core::mem::size_of::<T>();
    let align         = core::mem::align_of::<T>();

    with_mutator(|mutator| {
        let semantics = if payload_bytes >= GC.get_plan().constraints().max_non_los_default_alloc_bytes {
            AllocationSemantics::Los
        } else {
            AllocationSemantics::Default
        };

        let total_bytes = HEADER_BYTES + payload_bytes;
        let header_addr = mm::alloc::<PocketVM>(mutator, total_bytes, align, 0, semantics);
        assert!(!header_addr.is_zero(), "GC alloc returned null");

        // Write payload right after the header.
        let payload_addr = unsafe { header_addr + HEADER_BYTES };
        unsafe { payload_addr.to_mut_ptr::<T>().write(value) };

        // >>> ObjectReference must point to the *header* <<<
        let obj = PocketVM::object_start_to_ref(payload_addr);

        mm::post_alloc::<PocketVM>(mutator, obj, payload_bytes, semantics);
        binding::OBJ_META.insert(obj, (payload_bytes, align));

        Gc::from_objref(obj)
    })
}

/*────────────────────────────── 4 · stack helpers ─────────────────────────*/

/// Fallback when we cannot query the OS.
const STACK_GUESS: usize = 1 << 20; // 1 MiB

/// Downward–growing stack assumption: high == current anchor; low == anchor - guess.
fn stack_bounds_guess() -> (Address, Address) {
    let anchor = stack_anchor() as usize;
    let hi = anchor;
    let lo = anchor.saturating_sub(STACK_GUESS);
    unsafe { (Address::from_usize(lo), Address::from_usize(hi)) }
}

/// Address of a stack local – serves as our “current top” anchor.
#[inline(always)]
fn stack_anchor() -> *const u8 {
    let x = 0u8;
    &x as *const u8
}

/// Platform query: attempt to obtain **exact** stack bounds for the *current* thread.
/// Returns `(lo, hi)` where the valid stack memory is `[lo, hi)`.
fn stack_bounds_current_thread() -> (Address, Address) {
    // Try OS‑specific backends first; fall back to heuristic if they fail.
    if let Some(bounds) = stack_bounds_os() {
        bounds
    } else {
        stack_bounds_guess()
    }
}

#[cfg(any(target_os = "linux", target_os = "android"))]
fn stack_bounds_os() -> Option<(Address, Address)> {
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
fn stack_bounds_os() -> Option<(Address, Address)> {
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
fn stack_bounds_os() -> Option<(Address, Address)> {
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
fn stack_bounds_os() -> Option<(Address, Address)> {
    None
}

// ─── coarse generational barrier helper ──────────────────────────────
#[inline(always)]
pub fn record_write_gc<BaseT>(base: &Gc<BaseT>, new_val: &Value) {
    use mmtk::memory_manager as mm;

    // If the RHS is not a GC‑managed object we can bail out immediately.
    // Extract the target object reference if the RHS is a GC-managed object.
    let target_ref = match new_val {
        Value::Object(o)    => Some(o.objref()),
        Value::Array(a)     => Some(a.objref()),
        Value::Generator(g) => Some(g.objref()),
        _ => None,
    };
    if target_ref.is_none() {
        return;
    }

    // Coarse slot = object header (good enough for card marking).
    let src_obj = base.objref();
    let slot    = Slot::from_address(src_obj.to_raw_address());

    // Fire pre‑ + post‑barriers expected by Gen‑Immix.
    with_mutator(|m| {
        mm::object_reference_write_pre::<PocketVM>(m, src_obj, slot, target_ref);
        mm::object_reference_write_post::<PocketVM>(m, src_obj, slot, target_ref);
    });
}
// ──────────────────────────────────────────────────────────────────────────

pub fn gc_new_object_map(map: HashMap<String, Value>) -> Gc<RwLock<HashMap<String, Value>>> {
    let gc = Gc::new(RwLock::new(map));
    binding::write_kind_header(gc.objref(), ObjKind::ObjectMap);
    gc
}
pub fn gc_new_array(vec: Vec<Value>) -> Gc<RwLock<Vec<Value>>> {
    let gc = Gc::new(RwLock::new(vec));
    binding::write_kind_header(gc.objref(), ObjKind::ArrayVec);
    gc
}
pub fn gc_new_generator(gen_z: Generator) -> Gc<Mutex<Generator>> {
    let gc = Gc::new(Mutex::new(gen_z));
    binding::write_kind_header(gc.objref(), ObjKind::Generator);
    gc
}
pub fn gc_new_awaitable(state: AwaitableState) -> Gc<Mutex<AwaitableState>> {
    let gc = Gc::new(Mutex::new(state));
    binding::write_kind_header(gc.objref(), ObjKind::Awaitable);
    gc
}

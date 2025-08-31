// src/gc/binding.rs
use mmtk::vm::VMBinding;
use mmtk::vm::collection::GCThreadContext;
use mmtk::vm::active_plan;
use mmtk::vm::reference_glue;
use mmtk::vm::VMSlotTrait;
use mmtk::util::Address;
use mmtk::util::ObjectReference;
use mmtk::vm::collection;
pub struct NapalmVM;
impl Default for NapalmVM { fn default() -> Self { NapalmVM } }

impl VMBinding for NapalmVM {
    type VMSupport       = crate::gc::binding::support::Support;
    type VMObjectModel   = crate::gc::binding::NapalmObjectModel;   // <- inline
    type VMScanning      = crate::gc::binding::NapalmScanning;      // <- inline
    type VMActivePlan    = crate::gc::binding::support::ActivePlan;
    type VMCollection    = crate::gc::binding::support::Collection;
    type VMReferenceGlue = crate::gc::binding::support::ReferenceGlue;

    // Use the Slot you implemented in api.rs
    type VMSlot          = crate::gc::api::Slot;

    // Required by recent MMTk (fine to use the unimplemented slice for now)
    type VMMemorySlice   = mmtk::vm::slot::UnimplementedMemorySlice<Self::VMSlot>;
}

pub mod support {
    use core::ptr::NonNull;
    use once_cell::sync::Lazy;
    use parking_lot::RwLock;
    use parking_lot::Mutex;

    use mmtk::{Mutator};
    use mmtk::memory_manager;
    use mmtk::scheduler::GCWorker;
    use mmtk::util::opaque_pointer::{OpaquePointer, VMThread, VMMutatorThread, VMWorkerThread};
    use mmtk::util::{Address, ObjectReference};

    use crate::gc::mmtk::get_mmtk;

    // Re-export your Slot implementation from api.rs so `crate::gc::binding::Slot` exists.
    pub type Slot = crate::gc::api::Slot;

    pub struct Support;

    // --- tiny helper to make a per-thread opaque TLS token (no registry needed)
    thread_local! { static TLS_PROBE: u8 = 0; }
    #[inline(always)]
    fn current_vmthread() -> VMThread {
        let addr = TLS_PROBE.with(|p| mmtk::util::Address::from_ptr(p as *const u8));
        VMThread(mmtk::util::opaque_pointer::OpaquePointer::from_address(addr))
    }
    #[inline(always)] fn current_worker() -> VMWorkerThread { VMWorkerThread(current_vmthread()) }
    #[inline(always)] fn _current_mut() -> VMMutatorThread { VMMutatorThread(current_vmthread()) }

    // Minimal mutator-thread token required by bind_mutator().
    #[derive(Clone, Copy, Default)]
    pub struct MutatorThread;
    impl MutatorThread {
        #[inline(always)]
        pub fn current() -> VMMutatorThread { VMMutatorThread(current_vmthread()) }
    }

    #[derive(Clone, Copy, Default)]
    pub struct WorkerThread;
    impl WorkerThread {
        #[inline(always)]
        pub fn current() -> VMWorkerThread { VMWorkerThread(current_vmthread()) }
    }

    // ---- Mutator registry (for ActivePlan / stop-the-world) ----

    // We map VMThread -> Mutator*. We only touch this from VM threads (mutator attach/detach),
    // and GC threads (stop_all_mutators). Access is guarded by RwLock for simplicity.
    static REGISTRY: Lazy<RwLock<Vec<(VMThread, Mutex<Mutator<crate::gc::binding::NapalmVM>>)>>> = Lazy::new(|| RwLock::new(Vec::new()));

    /// Called after bind_mutator on the current (mutator) thread.
    pub unsafe fn register_current_thread_mutator(m: &mut Mutator<crate::gc::binding::NapalmVM>) {
        let tls = current_vmthread();
        let mut reg = REGISTRY.write().unwrap();
        let nn = NonNull::from(m);
        // Avoid dup if called twice defensively.
        if !reg.iter().any(|(t, p)| *t == tls && p.as_ptr() == nn.as_ptr()) {
            reg.push((tls, nn));
        }
    }

    /// Called before a mutator is dropped on the current (mutator) thread.
    pub unsafe fn unregister_current_thread_mutator(m_ptr: *mut Mutator<crate::gc::binding::NapalmVM>) {
        let tls = current_vmthread();
        let mut reg = REGISTRY.write().unwrap();
        if let Some(pos) = reg.iter().position(|(t, p)| *t == tls && p.as_ptr() == m_ptr) {
            reg.swap_remove(pos);
        }
    }

    #[inline(always)]
    fn find_mutator_by_tls<'a>(
        tls: VMMutatorThread
    ) -> Option<&'a mut Mutator<crate::gc::binding::NapalmVM>> {
        let vmthread = tls.0;
        // Take a snapshot of raw pointers while holding the read lock, then drop it.
        let ptr = {
            let reg = REGISTRY.read().unwrap();
            reg.iter().find(|(t, _)| *t == vmthread).map(|(_, p)| p.as_ptr())
        }?;
        // Safety: MMTk calls us at well-defined points (STW/stack-scan). We uphold their
        // lifetime expectations the same way other bindings do: we return a &'static mut from stored raw.
        Some(unsafe { &mut *ptr })
    }

    // ---- Collection ----
    pub struct Collection;

    impl collection::Collection<crate::gc::binding::NapalmVM> for Collection {
        #[inline(always)]
        fn stop_all_mutators<F>(_tls: VMWorkerThread, _visitor: F)
        where
            F: FnMut(&'static mut mmtk::Mutator<crate::gc::binding::NapalmVM>),
        {
            // Stub: cooperative STW not wired yet.
        }

        #[inline(always)]
        fn resume_mutators(_tls: VMWorkerThread) {
            // Stub
        }

        #[inline(always)]
        fn block_for_gc(_tls: VMMutatorThread) {
            // Stub
        }

        #[inline(always)]
        fn spawn_gc_thread(_parent: VMThread, ctx: GCThreadContext<crate::gc::binding::NapalmVM>) {
            if let GCThreadContext::Worker(worker) = ctx {
                let mmtk = get_mmtk();
                std::thread::Builder::new()
                    .name("mmtk-gc-worker".to_string())
                    .spawn(move || {
                        let tlsw = current_worker();
                        memory_manager::start_worker::<crate::gc::binding::NapalmVM>(tlsw, worker, mmtk);
                    })
                    .expect("Failed to spawn GC worker");
            }
        }
    }

    // ---- ActivePlan ----
    pub struct ActivePlan;

    impl active_plan::ActivePlan<crate::gc::binding::NapalmVM> for ActivePlan {
        #[inline(always)] fn is_mutator(_tls: VMThread) -> bool { false }   // stub
        #[inline(always)]
        fn mutator(_tls: VMMutatorThread) -> &'static mut mmtk::Mutator<crate::gc::binding::NapalmVM> {
            panic!("ActivePlan::mutator not wired yet");
        }
        #[inline(always)]
        fn mutators<'a>() -> Box<dyn Iterator<Item = &'a mut mmtk::Mutator<crate::gc::binding::NapalmVM>> + 'a> {
            Box::new(std::iter::empty())
        }
        #[inline(always)] fn number_of_mutators() -> usize { 0 }
    }

    // ---- Reference glue (weak/soft/phantom + finalizers) ----
    pub struct ReferenceGlue;

    impl reference_glue::ReferenceGlue<crate::gc::binding::NapalmVM> for ReferenceGlue {
        type FinalizableType = ObjectReference;
        #[inline(always)] fn clear_referent(_obj: ObjectReference) {}
        #[inline(always)] fn get_referent(_obj: ObjectReference) -> Option<ObjectReference> { None }
        #[inline(always)] fn set_referent(_r: ObjectReference, _to: ObjectReference) {}
        #[inline(always)] fn enqueue_references(_refs: &[ObjectReference], _tls: VMWorkerThread) {}
    }
}

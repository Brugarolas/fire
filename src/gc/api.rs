// src/gc/api.rs
use core::ptr;
use mmtk::{
    memory_manager,
    util::{Address, ObjectReference},
    AllocationSemantics, Mutator,
    vm::slot::Slot as SlotTrait,
};
use once_cell::sync::OnceCell;

use crate::gc::binding::{NapalmVM};
use crate::gc::binding::support::{MutatorThread, register_current_thread_mutator, unregister_current_thread_mutator};
use crate::gc::mmtk::get_mmtk;
use crate::value::{ValueRepr, is_ptr, NULL};

thread_local! {
    static TLS_MUTATOR: std::cell::RefCell<Option<Box<Mutator<NapalmVM>>>> =
        const { std::cell::RefCell::new(None) };
}

pub struct GcInit;
pub struct GcHandle;

impl GcInit {
    pub fn init() -> GcHandle {
        let _ = crate::gc::mmtk::init_mmtk_for_stickyimmix();
        GcHandle
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Slot(pub Address);
impl From<Address> for Slot { fn from(a: Address) -> Self { Slot(a) } }

type VM = NapalmVM;

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

    #[inline(always)]
    fn get_address(&self) -> Address { self.0 }
}

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

#[inline(always)]
pub unsafe fn post_alloc_object(obj_ptr: *mut u8, bytes: usize) {
    with_mutator(|mutator| {
        let objref = ObjectReference::from_raw_address(Address::from_mut_ptr(obj_ptr))
            .expect("post_alloc_object: null obj_ptr");
        memory_manager::post_alloc::<NapalmVM>(
            mutator, objref, bytes, AllocationSemantics::Default,
        );
    });
}

#[inline(always)]
pub unsafe fn post_write_barrier(object_base: *mut u8, slot: *mut ValueRepr, new_val: ValueRepr) {
    if is_ptr(new_val) && new_val != NULL {
        with_mutator(|mutator| {
            let src = ObjectReference::from_raw_address(Address::from_ptr(object_base))
                .expect("post barrier: null src");
            let vm_slot = VMSlot::from(Address::from_ptr(slot.cast::<u8>()));
            let target = ObjectReference::from_raw_address(Address::from_ptr(new_val as *mut u8));
            memory_manager::object_reference_write_post::<NapalmVM>(
                mutator, src, vm_slot, target
            );
        });
    }
}

#[inline(always)]
pub unsafe fn pre_write_barrier(object_base: *mut u8, slot: *mut ValueRepr) {
    let old_v: ValueRepr = unsafe { core::ptr::read(slot) };
    if is_ptr(old_v) && old_v != NULL {
        with_mutator(|mutator| {
            let src = ObjectReference::from_raw_address(Address::from_ptr(object_base))
                .expect("pre barrier: null src");
            let vm_slot = VMSlot::from(Address::from_ptr(slot.cast::<u8>()));
            let old = ObjectReference::from_raw_address(Address::from_ptr(old_v as *mut u8));
            memory_manager::object_reference_write_pre::<NapalmVM>(
                mutator, src, vm_slot, old
            );
        });
    }
}

pub unsafe fn alloc_raw(bytes: usize, align: usize) -> *mut u8 {
    with_mutator(|mutator| {
        let addr = memory_manager::alloc::<NapalmVM>(
            mutator, bytes, align, 0, AllocationSemantics::Default,
        );
        if addr.is_zero() { ptr::null_mut() } else { addr.to_mut_ptr::<u8>() }
    })
}

pub unsafe fn alloc_slow_path(bytes: usize, align: usize) -> *mut u8 {
    with_mutator(|mutator| {
        let addr = memory_manager::alloc_slow::<NapalmVM>(
            mutator, bytes, align, 0, AllocationSemantics::Default,
        );
        debug_assert!(!addr.is_zero());
        addr.to_mut_ptr::<u8>()
    })
}

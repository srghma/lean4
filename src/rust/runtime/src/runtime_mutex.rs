/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_mutex_impl {
    use std::sync::{Condvar, Mutex};
    use std::thread::ThreadId;

    unsafe fn external_data<T>(obj: *mut LeanObject) -> &'static T {
        &*lean_get_external_data(obj).cast::<T>()
    }

    unsafe fn alloc_external<T>(class: *mut LeanExternalClass, value: T) -> *mut LeanObject {
        lean_alloc_external(class, Box::into_raw(Box::new(value)).cast())
    }

    pub unsafe fn lean_io_basemutex_new() -> *mut LeanObject {
        alloc_external(BASEMUTEX_EXTERNAL_CLASS, BaseMutex::new())
    }

    pub unsafe fn lean_io_basemutex_lock(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseMutex>(mtx).lock();
        lean_box(0)
    }

    pub unsafe fn lean_io_basemutex_try_lock(mtx: *mut LeanObject) -> bool {
        external_data::<BaseMutex>(mtx).try_lock()
    }

    pub unsafe fn lean_io_basemutex_unlock(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseMutex>(mtx).unlock();
        lean_box(0)
    }

    pub unsafe fn lean_io_condvar_new() -> *mut LeanObject {
        alloc_external(CONDVAR_EXTERNAL_CLASS, RuntimeCondvar::new())
    }

    pub unsafe fn lean_io_condvar_wait(
        condvar: *mut LeanObject,
        mtx: *mut LeanObject,
    ) -> *mut LeanObject {
        external_data::<RuntimeCondvar>(condvar).wait(external_data::<BaseMutex>(mtx));
        lean_box(0)
    }

    pub unsafe fn lean_io_condvar_notify_one(condvar: *mut LeanObject) -> *mut LeanObject {
        external_data::<RuntimeCondvar>(condvar)
            .condvar
            .notify_one();
        lean_box(0)
    }

    pub unsafe fn lean_io_condvar_notify_all(condvar: *mut LeanObject) -> *mut LeanObject {
        external_data::<RuntimeCondvar>(condvar)
            .condvar
            .notify_all();
        lean_box(0)
    }

    pub unsafe fn lean_io_baserecmutex_new() -> *mut LeanObject {
        alloc_external(BASERECMUTEX_EXTERNAL_CLASS, BaseRecMutex::new())
    }

    pub unsafe fn lean_io_baserecmutex_lock(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseRecMutex>(mtx).lock();
        lean_box(0)
    }

    pub unsafe fn lean_io_baserecmutex_try_lock(mtx: *mut LeanObject) -> bool {
        external_data::<BaseRecMutex>(mtx).try_lock()
    }

    pub unsafe fn lean_io_baserecmutex_unlock(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseRecMutex>(mtx).unlock();
        lean_box(0)
    }

    pub unsafe fn lean_io_basesharedmutex_new() -> *mut LeanObject {
        alloc_external(BASESHAREDMUTEX_EXTERNAL_CLASS, BaseSharedMutex::new())
    }

    pub unsafe fn lean_io_basesharedmutex_write(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseSharedMutex>(mtx).write();
        lean_box(0)
    }

    pub unsafe fn lean_io_basesharedmutex_try_write(mtx: *mut LeanObject) -> bool {
        external_data::<BaseSharedMutex>(mtx).try_write()
    }

    pub unsafe fn lean_io_basesharedmutex_unlock_write(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseSharedMutex>(mtx).unlock_write();
        lean_box(0)
    }

    pub unsafe fn lean_io_basesharedmutex_read(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseSharedMutex>(mtx).read();
        lean_box(0)
    }

    pub unsafe fn lean_io_basesharedmutex_try_read(mtx: *mut LeanObject) -> bool {
        external_data::<BaseSharedMutex>(mtx).try_read()
    }

    pub unsafe fn lean_io_basesharedmutex_unlock_read(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseSharedMutex>(mtx).unlock_read();
        lean_box(0)
    }
}

pub use runtime_mutex_impl::*;

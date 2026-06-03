/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "std")]
mod runtime_mutex_impl {
    use super::*;
    use std::sync::{Condvar, Mutex};
    use std::thread::ThreadId;

    struct BaseMutex {
        locked: Mutex<bool>,
        changed: Condvar,
    }

    impl BaseMutex {
        fn new() -> Self {
            Self {
                locked: Mutex::new(false),
                changed: Condvar::new(),
            }
        }

        fn lock(&self) {
            let mut locked = self.locked.lock().unwrap();
            while *locked {
                locked = self.changed.wait(locked).unwrap();
            }
            *locked = true;
        }

        fn try_lock(&self) -> bool {
            let mut locked = self.locked.lock().unwrap();
            if *locked {
                false
            } else {
                *locked = true;
                true
            }
        }

        fn unlock(&self) {
            let mut locked = self.locked.lock().unwrap();
            *locked = false;
            self.changed.notify_one();
        }
    }

    struct RuntimeCondvar {
        condvar: Condvar,
    }

    impl RuntimeCondvar {
        fn new() -> Self {
            Self {
                condvar: Condvar::new(),
            }
        }

        fn wait(&self, mutex: &BaseMutex) {
            let mut locked = mutex.locked.lock().unwrap();
            *locked = false;
            mutex.changed.notify_one();
            locked = self.condvar.wait(locked).unwrap();
            while *locked {
                locked = mutex.changed.wait(locked).unwrap();
            }
            *locked = true;
        }
    }

    struct RecState {
        owner: Option<ThreadId>,
        depth: usize,
    }

    struct BaseRecMutex {
        state: Mutex<RecState>,
        changed: Condvar,
    }

    impl BaseRecMutex {
        fn new() -> Self {
            Self {
                state: Mutex::new(RecState {
                    owner: None,
                    depth: 0,
                }),
                changed: Condvar::new(),
            }
        }

        fn lock(&self) {
            let current = std::thread::current().id();
            let mut state = self.state.lock().unwrap();
            loop {
                match state.owner {
                    None => {
                        state.owner = Some(current);
                        state.depth = 1;
                        return;
                    }
                    Some(owner) if owner == current => {
                        state.depth += 1;
                        return;
                    }
                    _ => {
                        state = self.changed.wait(state).unwrap();
                    }
                }
            }
        }

        fn try_lock(&self) -> bool {
            let current = std::thread::current().id();
            let mut state = self.state.lock().unwrap();
            match state.owner {
                None => {
                    state.owner = Some(current);
                    state.depth = 1;
                    true
                }
                Some(owner) if owner == current => {
                    state.depth += 1;
                    true
                }
                _ => false,
            }
        }

        fn unlock(&self) {
            let current = std::thread::current().id();
            let mut state = self.state.lock().unwrap();
            if state.owner == Some(current) {
                state.depth -= 1;
                if state.depth == 0 {
                    state.owner = None;
                    self.changed.notify_one();
                }
            }
        }
    }

    struct SharedState {
        readers: usize,
        writer: bool,
    }

    struct BaseSharedMutex {
        state: Mutex<SharedState>,
        changed: Condvar,
    }

    impl BaseSharedMutex {
        fn new() -> Self {
            Self {
                state: Mutex::new(SharedState {
                    readers: 0,
                    writer: false,
                }),
                changed: Condvar::new(),
            }
        }

        fn write(&self) {
            let mut state = self.state.lock().unwrap();
            while state.writer || state.readers != 0 {
                state = self.changed.wait(state).unwrap();
            }
            state.writer = true;
        }

        fn try_write(&self) -> bool {
            let mut state = self.state.lock().unwrap();
            if state.writer || state.readers != 0 {
                false
            } else {
                state.writer = true;
                true
            }
        }

        fn unlock_write(&self) {
            let mut state = self.state.lock().unwrap();
            state.writer = false;
            self.changed.notify_all();
        }

        fn read(&self) {
            let mut state = self.state.lock().unwrap();
            while state.writer {
                state = self.changed.wait(state).unwrap();
            }
            state.readers += 1;
        }

        fn try_read(&self) -> bool {
            let mut state = self.state.lock().unwrap();
            if state.writer {
                false
            } else {
                state.readers += 1;
                true
            }
        }

        fn unlock_read(&self) {
            let mut state = self.state.lock().unwrap();
            if state.readers > 0 {
                state.readers -= 1;
                if state.readers == 0 {
                    self.changed.notify_all();
                }
            }
        }
    }

    static mut BASEMUTEX_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
    static mut CONDVAR_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
    static mut BASERECMUTEX_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
    static mut BASESHAREDMUTEX_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();

    unsafe extern "C" fn basemutex_finalizer(data: *mut c_void) {
        drop(Box::from_raw(data.cast::<BaseMutex>()));
    }

    unsafe extern "C" fn condvar_finalizer(data: *mut c_void) {
        drop(Box::from_raw(data.cast::<RuntimeCondvar>()));
    }

    unsafe extern "C" fn baserecmutex_finalizer(data: *mut c_void) {
        drop(Box::from_raw(data.cast::<BaseRecMutex>()));
    }

    unsafe extern "C" fn basesharedmutex_finalizer(data: *mut c_void) {
        drop(Box::from_raw(data.cast::<BaseSharedMutex>()));
    }

    unsafe extern "C" fn noop_foreach(_: *mut c_void, _: *mut LeanObject) {}

    unsafe fn external_data<T>(obj: *mut LeanObject) -> &'static T {
        &*lean_runtime_get_external_data(obj).cast::<T>()
    }

    unsafe fn alloc_external<T>(class: *mut LeanExternalClass, value: T) -> *mut LeanObject {
        lean_runtime_alloc_external(class, Box::into_raw(Box::new(value)).cast())
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basemutex_new() -> *mut LeanObject {
        alloc_external(BASEMUTEX_EXTERNAL_CLASS, BaseMutex::new())
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basemutex_lock(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseMutex>(mtx).lock();
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basemutex_try_lock(mtx: *mut LeanObject) -> u8 {
        external_data::<BaseMutex>(mtx).try_lock() as u8
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basemutex_unlock(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseMutex>(mtx).unlock();
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_condvar_new() -> *mut LeanObject {
        alloc_external(CONDVAR_EXTERNAL_CLASS, RuntimeCondvar::new())
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_condvar_wait(
        condvar: *mut LeanObject,
        mtx: *mut LeanObject,
    ) -> *mut LeanObject {
        external_data::<RuntimeCondvar>(condvar).wait(external_data::<BaseMutex>(mtx));
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_condvar_notify_one(condvar: *mut LeanObject) -> *mut LeanObject {
        external_data::<RuntimeCondvar>(condvar).condvar.notify_one();
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_condvar_notify_all(condvar: *mut LeanObject) -> *mut LeanObject {
        external_data::<RuntimeCondvar>(condvar).condvar.notify_all();
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_baserecmutex_new() -> *mut LeanObject {
        alloc_external(BASERECMUTEX_EXTERNAL_CLASS, BaseRecMutex::new())
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_baserecmutex_lock(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseRecMutex>(mtx).lock();
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_baserecmutex_try_lock(mtx: *mut LeanObject) -> u8 {
        external_data::<BaseRecMutex>(mtx).try_lock() as u8
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_baserecmutex_unlock(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseRecMutex>(mtx).unlock();
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basesharedmutex_new() -> *mut LeanObject {
        alloc_external(BASESHAREDMUTEX_EXTERNAL_CLASS, BaseSharedMutex::new())
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basesharedmutex_write(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseSharedMutex>(mtx).write();
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basesharedmutex_try_write(mtx: *mut LeanObject) -> u8 {
        external_data::<BaseSharedMutex>(mtx).try_write() as u8
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basesharedmutex_unlock_write(
        mtx: *mut LeanObject,
    ) -> *mut LeanObject {
        external_data::<BaseSharedMutex>(mtx).unlock_write();
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basesharedmutex_read(mtx: *mut LeanObject) -> *mut LeanObject {
        external_data::<BaseSharedMutex>(mtx).read();
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basesharedmutex_try_read(mtx: *mut LeanObject) -> u8 {
        external_data::<BaseSharedMutex>(mtx).try_read() as u8
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_basesharedmutex_unlock_read(
        mtx: *mut LeanObject,
    ) -> *mut LeanObject {
        external_data::<BaseSharedMutex>(mtx).unlock_read();
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean16initialize_mutexEv")]
    pub extern "C" fn initialize_mutex() {
        unsafe {
            BASEMUTEX_EXTERNAL_CLASS =
                lean_register_external_class(Some(basemutex_finalizer), Some(noop_foreach));
            CONDVAR_EXTERNAL_CLASS =
                lean_register_external_class(Some(condvar_finalizer), Some(noop_foreach));
            BASERECMUTEX_EXTERNAL_CLASS =
                lean_register_external_class(Some(baserecmutex_finalizer), Some(noop_foreach));
            BASESHAREDMUTEX_EXTERNAL_CLASS =
                lean_register_external_class(Some(basesharedmutex_finalizer), Some(noop_foreach));
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean14finalize_mutexEv")]
    pub extern "C" fn finalize_mutex() {}
}

#[cfg(feature = "std")]
pub use runtime_mutex_impl::*;

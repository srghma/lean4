use core::ffi::c_void;
use std::ptr;
use std::sync::{Condvar, Mutex};
use std::thread::ThreadId;

use leanh_l1::datatypes::LeanExternalClass;

use crate::r#priv::lean_register_external_class::lean_register_external_class;

static mut BASEMUTEX_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
static mut CONDVAR_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
static mut BASERECMUTEX_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
static mut BASESHAREDMUTEX_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();

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

unsafe fn basemutex_finalizer(data: *mut c_void) {
    drop(Box::from_raw(data.cast::<BaseMutex>()));
}

unsafe fn condvar_finalizer(data: *mut c_void) {
    drop(Box::from_raw(data.cast::<RuntimeCondvar>()));
}

unsafe fn baserecmutex_finalizer(data: *mut c_void) {
    drop(Box::from_raw(data.cast::<BaseRecMutex>()));
}

unsafe fn basesharedmutex_finalizer(data: *mut c_void) {
    drop(Box::from_raw(data.cast::<BaseSharedMutex>()));
}

pub fn initialize_mutex() {
    unsafe {
        BASEMUTEX_EXTERNAL_CLASS = lean_register_external_class(Some(basemutex_finalizer), None);
        CONDVAR_EXTERNAL_CLASS = lean_register_external_class(Some(condvar_finalizer), None);
        BASERECMUTEX_EXTERNAL_CLASS =
            lean_register_external_class(Some(baserecmutex_finalizer), None);
        BASESHAREDMUTEX_EXTERNAL_CLASS =
            lean_register_external_class(Some(basesharedmutex_finalizer), None);
    }
}

pub fn finalize_mutex() {}

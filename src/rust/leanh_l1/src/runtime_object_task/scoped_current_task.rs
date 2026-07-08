use crate::datatypes::LeanTaskObject;

// ─── Thread-local current task ────────────────────────────────────────────

std::thread_local! {
    static G_CURRENT_TASK: core::cell::Cell<*mut LeanTaskObject> =
        const { core::cell::Cell::new(core::ptr::null_mut()) };
}

pub fn current_task() -> *mut LeanTaskObject {
    G_CURRENT_TASK.with(|c| c.get())
}

pub fn set_current_task(t: *mut LeanTaskObject) {
    G_CURRENT_TASK.with(|c| c.set(t));
}
pub struct ScopedCurrentTask {
    prev: *mut LeanTaskObject,
}

impl ScopedCurrentTask {
    pub fn new(t: *mut LeanTaskObject) -> Self {
        let prev = current_task();
        set_current_task(t);
        ScopedCurrentTask { prev }
    }
}
impl Drop for ScopedCurrentTask {
    fn drop(&mut self) {
        set_current_task(self.prev);
    }
}

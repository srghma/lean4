use crate::runtime_object_task::task_manager::TaskManager;

pub fn initiate_shutdown(tm: &TaskManager) {
    let std_workers = {
        let mut guard = tm.inner.lock().unwrap();
        if guard.shutting_down {
            return;
        }
        guard.shutting_down = true;
        std::mem::take(&mut guard.std_workers)
    };
    tm.queue_cv.notify_all();
    for worker in std_workers {
        worker.join().expect("lean worker thread panicked");
    }
    let guard = tm.inner.lock().unwrap();
    let _guard = tm
        .dedicated_finished_cv
        .wait_while(guard, |g| g.num_dedicated_workers > 0)
        .unwrap();
}

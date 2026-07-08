use std::cell::Cell;

thread_local! {
    static G_MAX_HEARTBEAT: Cell<usize> = const { Cell::new(0) };
    static G_HEARTBEAT: Cell<usize> = const { Cell::new(0) };
}

pub fn reset_heartbeat() {
    G_HEARTBEAT.with(|cell| cell.set(0));
}

pub fn set_max_heartbeat(max: usize) {
    G_MAX_HEARTBEAT.with(|cell| cell.set(max));
}
pub fn get_max_heartbeat() -> usize {
    G_MAX_HEARTBEAT.with(|cell| cell.get())
}

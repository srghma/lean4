use leanh_l1::datatypes::{LeanObject, Size};
pub unsafe fn lean_initialize_runtime_module() {
    // initialize_alloc();
    // initialize_debug();
    // initialize_object was a no-op (object.cpp deleted)
    initialize_io();
    // initialize_thread();
    initialize_mutex();
    initialize_process();
    initialize_stack_overflow();
    initialize_libuv();
}

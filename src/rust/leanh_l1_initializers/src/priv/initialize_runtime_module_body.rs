use crate::{
    runtime_io_stream::initialize_io, runtime_libuv::initialize_libuv::initialize_libuv,
    runtime_mutex::initialize_mutex,
    runtime_stack_overflow::initialize_stack_overflow::initialize_stack_overflow,
};

pub(crate) unsafe fn initialize_runtime_module_body() {
    // initialize_alloc();
    // initialize_debug();
    // initialize_object was a no-op (object.cpp deleted)
    initialize_io();
    // initialize_thread();
    initialize_mutex();
    // initialize_process();
    initialize_stack_overflow();
    initialize_libuv();
}

use crate::{
    library_dynlib::initialize_dynlib::initialize_dynlib,
    library_util::lean_initialize_library_util::lean_initialize_library_util,
};

pub fn initialize_library_module() {
    // lean_cxx_initialize_num();
    unsafe { lean_initialize_library_util() };
    // initialize_time_task();
    initialize_dynlib();
    // initialize_ir_interpreter();
}

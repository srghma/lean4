use crate::r#priv::{
    initialize_name::initialize_name, initialize_name_generator::initialize_name_generator,
    initialize_options::initialize_options,
    initialize_runtime_module_body::initialize_runtime_module_body,
};

pub fn initialize_util_module() {
    unsafe { initialize_runtime_module_body() };
    // initialize_ascii();
    initialize_name();
    initialize_name_generator();
    initialize_options();
}

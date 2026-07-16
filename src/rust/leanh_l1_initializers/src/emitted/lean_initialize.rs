use leanh_l1::{datatypes::LeanObject, runtime_stack_info::save_stack_info};

use crate::r#priv::{
    consume_io_result::consume_io_result,
    initialize_constructions_module::initialize_constructions_module,
    initialize_kernel_module::initialize_kernel_module,
    initialize_library_core_module::initialize_library_core_module,
    initialize_library_module::initialize_library_module,
    initialize_util_module::initialize_util_module,
};

type ModuleInitializer = unsafe fn(bool) -> *mut LeanObject;

pub fn lean_initialize(
    initialize_Init: ModuleInitializer,
    initialize_Std: ModuleInitializer,
    initialize_Lean: ModuleInitializer,
) {
    save_stack_info(true);
    initialize_util_module();
    let builtin = true;
    unsafe { consume_io_result(initialize_Init(builtin)) };
    unsafe { consume_io_result(initialize_Std(builtin)) };
    unsafe { consume_io_result(initialize_Lean(builtin)) };
    initialize_kernel_module();
    // init_default_print_fn();
    initialize_library_core_module();
    initialize_library_module();
    initialize_constructions_module();
}

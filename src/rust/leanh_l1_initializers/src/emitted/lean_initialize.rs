use leanh_l1::datatypes::{LeanObject, Size};

pub fn lean_initialize() {
    save_stack_info(true);
    initialize_util_module();
    let builtin = true;
    consume_io_result(initialize_Init(builtin));
    consume_io_result(initialize_Std(builtin));
    consume_io_result(initialize_Lean(builtin));
    initialize_kernel_module();
    init_default_print_fn();
    initialize_library_core_module();
    initialize_library_module();
    initialize_constructions_module();
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_cxx_initialize_llvm() {}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_cxx_finalize_llvm() {}

unsafe fn llvm_disabled_error() -> *mut LeanObject {
    let msg = c"Lean was built without LLVM support";
    lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg.as_ptr())))
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_init_llvm() -> *mut LeanObject {
    unsafe { llvm_disabled_error() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_emit_llvm(
    _env: *mut LeanObject,
    _mod_name: *mut LeanObject,
    _filepath: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { llvm_disabled_error() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_llvm_initialize_target_info() -> *mut LeanObject {
    unsafe { lean_box(0) }
}

macro_rules! stub_size_t {
    ($name:ident ( $($arg:ident : $ty:ty),* )) => {
        #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
        pub extern "C" fn $name($($arg: $ty),*) -> usize {
            0
        }
    };
}

macro_rules! stub_io_obj {
    ($name:ident ( $($arg:ident : $ty:ty),* )) => {
        #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
        pub extern "C" fn $name($($arg: $ty),*) -> *mut LeanObject {
            unsafe { llvm_disabled_error() }
        }
    };
}

stub_size_t!(lean_llvm_create_context());
stub_size_t!(lean_llvm_create_module(ctx: usize, name: *mut LeanObject));
stub_io_obj!(lean_llvm_write_bitcode_to_file(ctx: usize, mod_: usize, filepath: *mut LeanObject));
stub_io_obj!(lean_llvm_module_to_string(ctx: usize, mod_: usize));
stub_size_t!(lean_llvm_add_function(ctx: usize, mod_: usize, name: *mut LeanObject, ty: usize, linkage: usize));
stub_io_obj!(lean_llvm_get_named_function(ctx: usize, mod_: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_add_global(ctx: usize, mod_: usize, name: *mut LeanObject, ty: usize));
stub_io_obj!(lean_llvm_get_named_global(ctx: usize, mod_: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_global_string(ctx: usize, builder: usize, value: *mut LeanObject, name: *mut LeanObject));
stub_io_obj!(lean_llvm_set_initializer(ctx: usize, global: usize, val: usize));
stub_io_obj!(llvm_is_declaration(ctx: usize, global: usize));
stub_io_obj!(lean_llvm_get_first_function(ctx: usize, mod_: usize));
stub_io_obj!(lean_llvm_get_next_function(ctx: usize, function: usize));
stub_io_obj!(lean_llvm_get_first_global(ctx: usize, mod_: usize));
stub_io_obj!(lean_llvm_get_next_global(ctx: usize, global: usize));

// Keep the rest of the LLVM surface available if any downstream code reaches it.
stub_size_t!(lean_llvm_get_undef(ctx: usize, ty: usize));
stub_size_t!(lean_llvm_function_type(ctx: usize, ret: usize, args: *mut *mut LeanObject, is_var_arg: u32));
stub_size_t!(lean_llvm_opaque_pointer_type_in_context(ctx: usize));
stub_size_t!(lean_llvm_int_type_in_context(ctx: usize, width: u64));
stub_size_t!(lean_llvm_float_type_in_context(ctx: usize));
stub_size_t!(lean_llvm_void_type_in_context(ctx: usize));
stub_size_t!(lean_llvm_double_type_in_context(ctx: usize));
stub_size_t!(lean_llvm_pointer_type(ctx: usize, base: usize));
stub_size_t!(lean_llvm_array_type(ctx: usize, base: usize, nelem: u64));
stub_size_t!(lean_llvm_create_builder_in_context(ctx: usize));
stub_size_t!(lean_llvm_append_basic_block_in_context(ctx: usize, fn_: usize, name: *mut LeanObject));
stub_io_obj!(lean_llvm_position_builder_at_end(ctx: usize, builder: usize, bb: usize));
stub_io_obj!(lean_llvm_position_builder_before(ctx: usize, builder: usize, instr: usize));
stub_io_obj!(lean_llvm_clear_insertion_position(ctx: usize, builder: usize));
stub_size_t!(lean_llvm_build_call2(ctx: usize, builder: usize, fn_: usize, args: *mut *mut LeanObject, nargs: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_cond_br(ctx: usize, builder: usize, cond: usize, then_bb: usize, else_bb: usize));
stub_size_t!(lean_llvm_build_br(ctx: usize, builder: usize, bb: usize));
stub_io_obj!(lean_llvm_build_store(ctx: usize, builder: usize, val: usize, ptr_: usize));
stub_size_t!(lean_llvm_build_load2(ctx: usize, builder: usize, ptr_: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_alloca(ctx: usize, builder: usize, ty: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_ret(ctx: usize, builder: usize, v: usize));
stub_size_t!(lean_llvm_build_ret_void(builder: usize));
stub_size_t!(lean_llvm_build_unreachable(ctx: usize, builder: usize));
stub_size_t!(lean_llvm_build_inbounds_gep2(ctx: usize, builder: usize, ty: usize, ptr_: usize, idx: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_gep2(ctx: usize, builder: usize, ty: usize, ptr_: usize, idx: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_sext(ctx: usize, builder: usize, v: usize, ty: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_zext(ctx: usize, builder: usize, v: usize, ty: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_sext_or_trunc(ctx: usize, builder: usize, v: usize, ty: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_switch(ctx: usize, builder: usize, v: usize, default_bb: usize, cases: *mut *mut LeanObject));
stub_size_t!(lean_llvm_build_ptr_to_int(ctx: usize, builder: usize, v: usize, ty: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_mul(ctx: usize, builder: usize, a: usize, b: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_add(ctx: usize, builder: usize, a: usize, b: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_sub(ctx: usize, builder: usize, a: usize, b: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_not(ctx: usize, builder: usize, v: usize, name: *mut LeanObject));
stub_size_t!(lean_llvm_build_icmp(ctx: usize, builder: usize, pred: usize, a: usize, b: usize, name: *mut LeanObject));
stub_io_obj!(lean_llvm_add_case(ctx: usize, switch_: usize, val: usize, bb: usize));
stub_size_t!(lean_llvm_get_basic_block_parent(ctx: usize, bb: usize));
stub_size_t!(lean_llvm_get_insert_block(ctx: usize, builder: usize));
stub_size_t!(lean_llvm_type_of(ctx: usize, val: usize));
stub_io_obj!(lean_llvm_print_module_to_string(ctx: usize, mod_: usize));
stub_io_obj!(lean_llvm_print_module_to_file(ctx: usize, mod_: usize, filepath: *mut LeanObject));
stub_size_t!(lean_llvm_const_int(ctx: usize, ty: usize, val: u64, sign_extend: c_uint));
stub_size_t!(lean_llvm_const_array(ctx: usize, ty: usize, values: *mut *mut LeanObject, n: usize));
stub_size_t!(lean_llvm_const_string(ctx: usize, s: *mut LeanObject, null_terminated: u32));
stub_size_t!(lean_llvm_const_pointer_null(ctx: usize, ty: usize));
stub_io_obj!(lean_llvm_set_tail_call(ctx: usize, call: usize, value: c_uint));
stub_size_t!(lean_llvm_create_memory_buffer_with_contents_of_file(ctx: usize, path: *mut LeanObject));
stub_size_t!(lean_llvm_parse_bitcode(ctx: usize, buffer: usize));
stub_io_obj!(lean_llvm_link_modules(ctx: usize, dest: usize, src: usize));
stub_size_t!(lean_llvm_create_target_machine(ctx: usize, triple: *mut LeanObject, cpu: *mut LeanObject, features: *mut LeanObject, opt: c_uint, reloc: c_uint, code_model: c_uint));
stub_size_t!(lean_llvm_get_target_from_triple(ctx: usize, triple: *mut LeanObject));
stub_io_obj!(lean_llvm_get_default_target_triple());
stub_io_obj!(lean_llvm_target_machine_emit_to_file(ctx: usize, tm: usize, mod_: usize, filepath: *mut LeanObject));
stub_io_obj!(lean_llvm_dispose_target_machine(ctx: usize, tm: usize));
stub_io_obj!(lean_llvm_dispose_module(ctx: usize, mod_: usize));
stub_io_obj!(lean_llvm_set_visibility(ctx: usize, value: usize, vis: u64));
stub_io_obj!(lean_llvm_set_dll_storage_class(ctx: usize, value: usize, cls: u64));
stub_size_t!(lean_llvm_create_string_attribute(ctx: usize, key: *mut LeanObject, value: *mut LeanObject));
stub_io_obj!(lean_llvm_add_attribute_at_index(ctx: usize, fn_: usize, idx: u64, attr: usize));
stub_io_obj!(lean_llvm_set_linkage(ctx: usize, value: usize, linkage: u64));
stub_io_obj!(lean_llvm_get_value_name2(ctx: usize, value: usize));
stub_io_obj!(lean_llvm_verify_module(ctx: usize, mod_: usize));
stub_size_t!(lean_llvm_count_basic_blocks(ctx: usize, fn_val: usize));
stub_size_t!(lean_llvm_get_entry_basic_block(ctx: usize, fn_val: usize));
stub_io_obj!(lean_llvm_get_first_instruction(ctx: usize, bb: usize));

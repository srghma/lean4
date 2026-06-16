/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_llvm_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_init_llvm() -> *mut LeanObject;
        fn lean_cxx_emit_llvm(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_initialize_target_info() -> *mut LeanObject;
        fn lean_cxx_llvm_create_context() -> usize;
        fn lean_cxx_llvm_create_module(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_write_bitcode_to_file(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_module_to_string(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_add_function(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_named_function(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_add_global(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_named_global(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_build_global_string(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_undef(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_set_initializer(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_function_type(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_opaque_pointer_type_in_context(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_int_type_in_context(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_float_type_in_context(p0: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_void_type_in_context(p0: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_double_type_in_context(p0: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_pointer_type(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_array_type(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_create_builder_in_context(p0: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_append_basic_block_in_context(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_position_builder_at_end(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_clear_insertion_position(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_build_call2(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject, p5: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_cond_br(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_br(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_store(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_build_load2(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_alloca(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_ret(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_ret_void(p0: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_unreachable(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_inbounds_gep2(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject, p5: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_gep2(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject, p5: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_sext(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_zext(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_sext_or_trunc(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_switch(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_ptr_to_int(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_mul(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_add(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_sub(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_not(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_build_icmp(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject, p5: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_add_case(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_get_basic_block_parent(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_insert_block(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_type_of(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_print_module_to_string(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_print_module_to_file(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_const_int(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_const_array(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_const_string(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_const_pointer_null(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_param(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_count_params(p0: *mut LeanObject, p1: *mut LeanObject) -> u64;
        fn lean_cxx_llvm_set_tail_call(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_parse_bitcode(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_link_modules(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_create_target_machine(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_target_from_triple(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_default_target_triple() -> *mut LeanObject;
        fn lean_cxx_llvm_target_machine_emit_to_file(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_dispose_target_machine(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_dispose_module(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_set_visibility(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_set_dll_storage_class(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_add_attribute_at_index(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_get_first_global(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_next_global(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_first_function(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_next_function(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_set_linkage(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_get_value_name2(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_is_declaration(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_verify_module(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_count_basic_blocks(p0: *mut LeanObject, p1: *mut LeanObject) -> u64;
        fn lean_cxx_llvm_get_entry_basic_block(p0: *mut LeanObject, p1: *mut LeanObject) -> usize;
        fn lean_cxx_llvm_get_first_instruction(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_llvm_position_builder_before(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_init_llvm() -> *mut LeanObject {
        lean_cxx_init_llvm()
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_emit_llvm(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_emit_llvm(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_initialize_target_info() -> *mut LeanObject {
        lean_cxx_llvm_initialize_target_info()
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_create_context() -> usize {
        lean_cxx_llvm_create_context()
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_create_module(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_create_module(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_write_bitcode_to_file(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_write_bitcode_to_file(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_module_to_string(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_module_to_string(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_add_function(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize {
        lean_cxx_llvm_add_function(p0, p1, p2, p3)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_named_function(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_get_named_function(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_add_global(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize {
        lean_cxx_llvm_add_global(p0, p1, p2, p3)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_named_global(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_get_named_global(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_global_string(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_global_string(p0, p1, p2, p3)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_undef(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_get_undef(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_set_initializer(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_set_initializer(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_function_type(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize {
        lean_cxx_llvm_function_type(p0, p1, p2, p3)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_opaque_pointer_type_in_context(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_opaque_pointer_type_in_context(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_int_type_in_context(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_int_type_in_context(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_float_type_in_context(p0: *mut LeanObject) -> usize {
        lean_cxx_llvm_float_type_in_context(p0)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_void_type_in_context(p0: *mut LeanObject) -> usize {
        lean_cxx_llvm_void_type_in_context(p0)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_double_type_in_context(p0: *mut LeanObject) -> usize {
        lean_cxx_llvm_double_type_in_context(p0)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_pointer_type(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_pointer_type(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_array_type(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize {
        lean_cxx_llvm_array_type(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_create_builder_in_context(p0: *mut LeanObject) -> usize {
        lean_cxx_llvm_create_builder_in_context(p0)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_append_basic_block_in_context(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize {
        lean_cxx_llvm_append_basic_block_in_context(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_position_builder_at_end(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_position_builder_at_end(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_clear_insertion_position(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_clear_insertion_position(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_call2(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject, p5: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_call2(p0, p1, p2, p3, p4, p5)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_cond_br(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_cond_br(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_br(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_br(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_store(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_build_store(p0, p1, p2, p3)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_load2(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_load2(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_alloca(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_alloca(p0, p1, p2, p3)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_ret(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_ret(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_ret_void(p0: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_ret_void(p0)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_unreachable(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_unreachable(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_inbounds_gep2(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject, p5: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_inbounds_gep2(p0, p1, p2, p3, p4, p5)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_gep2(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject, p5: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_gep2(p0, p1, p2, p3, p4, p5)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_sext(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_sext(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_zext(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_zext(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_sext_or_trunc(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_sext_or_trunc(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_switch(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_switch(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_ptr_to_int(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_ptr_to_int(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_mul(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_mul(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_add(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_add(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_sub(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_sub(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_not(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_not(p0, p1, p2, p3)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_build_icmp(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject, p5: *mut LeanObject) -> usize {
        lean_cxx_llvm_build_icmp(p0, p1, p2, p3, p4, p5)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_add_case(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_add_case(p0, p1, p2, p3)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_basic_block_parent(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_get_basic_block_parent(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_insert_block(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_get_insert_block(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_type_of(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_type_of(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_print_module_to_string(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_print_module_to_string(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_print_module_to_file(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_print_module_to_file(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_const_int(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> usize {
        lean_cxx_llvm_const_int(p0, p1, p2, p3)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_const_array(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize {
        lean_cxx_llvm_const_array(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_const_string(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_const_string(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_const_pointer_null(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_const_pointer_null(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn llvm_get_param(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> usize {
        lean_cxx_llvm_get_param(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn llvm_count_params(p0: *mut LeanObject, p1: *mut LeanObject) -> u64 {
        lean_cxx_llvm_count_params(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_set_tail_call(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_set_tail_call(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_parse_bitcode(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_parse_bitcode(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_link_modules(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_link_modules(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_create_target_machine(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> usize {
        lean_cxx_llvm_create_target_machine(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_target_from_triple(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_get_target_from_triple(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_default_target_triple() -> *mut LeanObject {
        lean_cxx_llvm_get_default_target_triple()
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_target_machine_emit_to_file(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject, p4: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_target_machine_emit_to_file(p0, p1, p2, p3, p4)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_dispose_target_machine(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_dispose_target_machine(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_dispose_module(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_dispose_module(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_set_visibility(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_set_visibility(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_set_dll_storage_class(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_set_dll_storage_class(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_add_attribute_at_index(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject, p3: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_add_attribute_at_index(p0, p1, p2, p3)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_first_global(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_get_first_global(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_next_global(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_get_next_global(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_first_function(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_get_first_function(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_next_function(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_get_next_function(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_set_linkage(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_set_linkage(p0, p1, p2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_value_name2(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_get_value_name2(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn llvm_is_declaration(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_is_declaration(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_verify_module(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_verify_module(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_count_basic_blocks(p0: *mut LeanObject, p1: *mut LeanObject) -> u64 {
        lean_cxx_llvm_count_basic_blocks(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_entry_basic_block(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {
        lean_cxx_llvm_get_entry_basic_block(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_get_first_instruction(p0: *mut LeanObject, p1: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_get_first_instruction(p0, p1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_llvm_position_builder_before(p0: *mut LeanObject, p1: *mut LeanObject, p2: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_llvm_position_builder_before(p0, p1, p2)
    }

}
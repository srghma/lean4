// Lean compiler output
// Module: Init.Syntax
// Imports: Init.Prelude Init.Data.Array.Set
use crate::ffi::{lean_array_fset, lean_array_get_size, lean_nat_dec_lt};
use crate::r#gen::Init::Data::Array::Set::{
    initialize_Init_Data_Array_Set, runtime_initialize_Init_Data_Array_Set,
};
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
pub unsafe fn l_Lean_Syntax_setArgs(
    mut v_stx_36_: *mut leanh::LeanObject,
    mut v_args_37_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_38_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_39_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_42_: u8 = 0;
    let mut v___x_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_45_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_46_: u8 = 0;
    let mut v_unused_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_stx_36_) == 1 {
                    v_info_38_ = leanh::lean_ctor_get(v_stx_36_, 0);
                    v_kind_39_ = leanh::lean_ctor_get(v_stx_36_, 1);
                    v_isSharedCheck_46_ = (!leanh::lean_is_exclusive(v_stx_36_)) as u8;
                    if v_isSharedCheck_46_ == 0 {
                        v_unused_47_ = leanh::lean_ctor_get(v_stx_36_, 2);
                        leanh::lean_dec(v_unused_47_);
                        v___x_41_ = v_stx_36_;
                        v_isShared_42_ = v_isSharedCheck_46_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_kind_39_);
                        leanh::lean_inc(v_info_38_);
                        leanh::lean_dec(v_stx_36_);
                        v___x_41_ = leanh::lean_box(0);
                        v_isShared_42_ = v_isSharedCheck_46_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_args_37_);
                    return v_stx_36_;
                }
            }
            1 => {
                if v_isShared_42_ == 0 {
                    leanh::lean_ctor_set(v___x_41_, 2, v_args_37_);
                    v___x_44_ = v___x_41_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_45_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_45_, 0, v_info_38_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_45_, 1, v_kind_39_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_45_, 2, v_args_37_);
                    v___x_44_ = v_reuseFailAlloc_45_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_44_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_setArg(
    mut v_stx_48_: *mut leanh::LeanObject,
    mut v_i_49_: *mut leanh::LeanObject,
    mut v_arg_50_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_51_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: u8 = 0;
    let mut v___x_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_58_: u8 = 0;
    let mut v___x_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_63_: u8 = 0;
    let mut v_unused_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_stx_48_) == 1 {
                    v_info_51_ = leanh::lean_ctor_get(v_stx_48_, 0);
                    v_kind_52_ = leanh::lean_ctor_get(v_stx_48_, 1);
                    v_args_53_ = leanh::lean_ctor_get(v_stx_48_, 2);
                    v___x_54_ = lean_array_get_size(v_args_53_);
                    v___x_55_ = lean_nat_dec_lt(v_i_49_, v___x_54_);
                    if v___x_55_ == 0 {
                        leanh::lean_dec(v_arg_50_);
                        return v_stx_48_;
                    } else {
                        leanh::lean_inc_ref(v_args_53_);
                        leanh::lean_inc(v_kind_52_);
                        leanh::lean_inc(v_info_51_);
                        v_isSharedCheck_63_ = (!leanh::lean_is_exclusive(v_stx_48_)) as u8;
                        if v_isSharedCheck_63_ == 0 {
                            v_unused_64_ = leanh::lean_ctor_get(v_stx_48_, 2);
                            leanh::lean_dec(v_unused_64_);
                            v_unused_65_ = leanh::lean_ctor_get(v_stx_48_, 1);
                            leanh::lean_dec(v_unused_65_);
                            v_unused_66_ = leanh::lean_ctor_get(v_stx_48_, 0);
                            leanh::lean_dec(v_unused_66_);
                            v___x_57_ = v_stx_48_;
                            v_isShared_58_ = v_isSharedCheck_63_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_stx_48_);
                            v___x_57_ = leanh::lean_box(0);
                            v_isShared_58_ = v_isSharedCheck_63_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_arg_50_);
                    return v_stx_48_;
                }
            }
            1 => {
                v___x_59_ = lean_array_fset(v_args_53_, v_i_49_, v_arg_50_);
                if v_isShared_58_ == 0 {
                    leanh::lean_ctor_set(v___x_57_, 2, v___x_59_);
                    v___x_61_ = v___x_57_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_62_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_62_, 0, v_info_51_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_62_, 1, v_kind_52_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_62_, 2, v___x_59_);
                    v___x_61_ = v_reuseFailAlloc_62_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_61_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_setArg___boxed(
    mut v_stx_67_: *mut leanh::LeanObject,
    mut v_i_68_: *mut leanh::LeanObject,
    mut v_arg_69_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_70_ = l_Lean_Syntax_setArg(v_stx_67_, v_i_68_, v_arg_69_);
    leanh::lean_dec(v_i_68_);
    return v_res_70_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Syntax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Syntax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Syntax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Syntax(builtin);
}
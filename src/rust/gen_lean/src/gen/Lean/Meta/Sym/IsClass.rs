// Lean compiler output
// Module: Lean.Meta.Sym.IsClass
// Imports: Lean.Meta.Sym.SymM
use crate::r#gen::Lean::Class::lean_is_class;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
pub unsafe fn l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(
    mut v_env_19_: *mut leanh::LeanObject,
    mut v_a_20_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_21_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_22_: u8 = 0;
    let mut v___x_23_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_24_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_25_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_27_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_29_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_31_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_20_) {
                4 => {
                    v_declName_21_ = leanh::lean_ctor_get(v_a_20_, 0);
                    leanh::lean_inc_n(v_declName_21_, 2);
                    leanh::lean_dec_ref_known(v_a_20_, 2);
                    v___x_22_ = lean_is_class(v_env_19_, v_declName_21_);
                    if v___x_22_ == 0 {
                        leanh::lean_dec(v_declName_21_);
                        v___x_23_ = leanh::lean_box(0);
                        return v___x_23_;
                    } else {
                        v___x_24_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_24_, 0, v_declName_21_);
                        return v___x_24_;
                    }
                }
                5 => {
                    v_fn_25_ = leanh::lean_ctor_get(v_a_20_, 0);
                    leanh::lean_inc_ref(v_fn_25_);
                    leanh::lean_dec_ref_known(v_a_20_, 2);
                    v_a_20_ = v_fn_25_;
                    state = 0;
                    continue;
                }
                7 => {
                    v_body_27_ = leanh::lean_ctor_get(v_a_20_, 2);
                    leanh::lean_inc_ref(v_body_27_);
                    leanh::lean_dec_ref_known(v_a_20_, 3);
                    v_a_20_ = v_body_27_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_body_29_ = leanh::lean_ctor_get(v_a_20_, 3);
                    leanh::lean_inc_ref(v_body_29_);
                    leanh::lean_dec_ref_known(v_a_20_, 4);
                    v_a_20_ = v_body_29_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_expr_31_ = leanh::lean_ctor_get(v_a_20_, 1);
                    leanh::lean_inc_ref(v_expr_31_);
                    leanh::lean_dec_ref_known(v_a_20_, 2);
                    v_a_20_ = v_expr_31_;
                    state = 0;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v_a_20_);
                    leanh::lean_dec_ref(v_env_19_);
                    v___x_33_ = leanh::lean_box(0);
                    return v___x_33_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isClass_x3f(
    mut v_env_34_: *mut leanh::LeanObject,
    mut v_type_35_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_36_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_36_ =
        l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(v_env_34_, v_type_35_);
    return v___x_36_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_IsClass(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_IsClass(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_IsClass(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_IsClass(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_IsClass(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_IsClass(builtin);
}
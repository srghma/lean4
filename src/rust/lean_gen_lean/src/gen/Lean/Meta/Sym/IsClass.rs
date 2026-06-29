// Lean compiler output
// Module: Lean.Meta.Sym.IsClass
// Imports: Lean.Meta.Sym.SymM
use crate::r#gen::Lean::Class::lean_is_class;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
pub unsafe fn l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(
    mut v_env_19_: *mut crate::leanh::LeanObject,
    mut v_a_20_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_21_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_22_: u8 = 0;
    let mut v___x_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_25_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_27_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_20_) {
                4 => {
                    v_declName_21_ = crate::leanh::lean_ctor_get(v_a_20_, 0);
                    crate::leanh::lean_inc_n(v_declName_21_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_20_, 2);
                    v___x_22_ = lean_is_class(v_env_19_, v_declName_21_);
                    if v___x_22_ == 0 {
                        crate::leanh::lean_dec(v_declName_21_);
                        v___x_23_ = crate::leanh::lean_box(0);
                        return v___x_23_;
                    } else {
                        v___x_24_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_24_, 0, v_declName_21_);
                        return v___x_24_;
                    }
                }
                5 => {
                    v_fn_25_ = crate::leanh::lean_ctor_get(v_a_20_, 0);
                    crate::leanh::lean_inc_ref(v_fn_25_);
                    crate::leanh::lean_dec_ref_known(v_a_20_, 2);
                    v_a_20_ = v_fn_25_;
                    state = 0;
                    continue;
                }
                7 => {
                    v_body_27_ = crate::leanh::lean_ctor_get(v_a_20_, 2);
                    crate::leanh::lean_inc_ref(v_body_27_);
                    crate::leanh::lean_dec_ref_known(v_a_20_, 3);
                    v_a_20_ = v_body_27_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_body_29_ = crate::leanh::lean_ctor_get(v_a_20_, 3);
                    crate::leanh::lean_inc_ref(v_body_29_);
                    crate::leanh::lean_dec_ref_known(v_a_20_, 4);
                    v_a_20_ = v_body_29_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_expr_31_ = crate::leanh::lean_ctor_get(v_a_20_, 1);
                    crate::leanh::lean_inc_ref(v_expr_31_);
                    crate::leanh::lean_dec_ref_known(v_a_20_, 2);
                    v_a_20_ = v_expr_31_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_a_20_);
                    crate::leanh::lean_dec_ref(v_env_19_);
                    v___x_33_ = crate::leanh::lean_box(0);
                    return v___x_33_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isClass_x3f(
    mut v_env_34_: *mut crate::leanh::LeanObject,
    mut v_type_35_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_36_ =
        l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(v_env_34_, v_type_35_);
    return v___x_36_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_IsClass(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_IsClass(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_IsClass(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_IsClass(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_IsClass(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_IsClass(builtin);
}

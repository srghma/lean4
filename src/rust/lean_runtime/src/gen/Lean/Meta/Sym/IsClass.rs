// Lean compiler output
// Module: Lean.Meta.Sym.IsClass
// Imports: Lean.Meta.Sym.SymM
use crate::r#gen::Lean::Class::lean_is_class;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(
    mut v_env_19_: *mut LeanObject,
    mut v_a_20_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_21_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_22_: u8 = 0;
    let mut v___x_23_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_24_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_25_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_27_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_29_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_31_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_20_) {
                4 => {
                    v_declName_21_ = lean_ctor_get(v_a_20_, 0);
                    lean_inc_n(v_declName_21_, 2);
                    lean_dec_ref_known(v_a_20_, 2);
                    v___x_22_ = lean_is_class(v_env_19_, v_declName_21_);
                    if v___x_22_ == 0 {
                        lean_dec(v_declName_21_);
                        v___x_23_ = lean_box(0);
                        return v___x_23_;
                    } else {
                        v___x_24_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_24_, 0, v_declName_21_);
                        return v___x_24_;
                    }
                }
                5 => {
                    v_fn_25_ = lean_ctor_get(v_a_20_, 0);
                    lean_inc_ref(v_fn_25_);
                    lean_dec_ref_known(v_a_20_, 2);
                    v_a_20_ = v_fn_25_;
                    state = 0;
                    continue;
                }
                7 => {
                    v_body_27_ = lean_ctor_get(v_a_20_, 2);
                    lean_inc_ref(v_body_27_);
                    lean_dec_ref_known(v_a_20_, 3);
                    v_a_20_ = v_body_27_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_body_29_ = lean_ctor_get(v_a_20_, 3);
                    lean_inc_ref(v_body_29_);
                    lean_dec_ref_known(v_a_20_, 4);
                    v_a_20_ = v_body_29_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_expr_31_ = lean_ctor_get(v_a_20_, 1);
                    lean_inc_ref(v_expr_31_);
                    lean_dec_ref_known(v_a_20_, 2);
                    v_a_20_ = v_expr_31_;
                    state = 0;
                    continue;
                }
                _ => {
                    lean_dec_ref(v_a_20_);
                    lean_dec_ref(v_env_19_);
                    v___x_33_ = lean_box(0);
                    return v___x_33_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isClass_x3f(
    mut v_env_34_: *mut LeanObject,
    mut v_type_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    v___x_36_ =
        l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClass_x3f_go(v_env_34_, v_type_35_);
    return v___x_36_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_IsClass(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_IsClass(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_IsClass(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_IsClass(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_IsClass(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_IsClass(builtin);
}

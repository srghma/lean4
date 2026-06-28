// Lean compiler output
// Module: Init.Data.List.ToArrayImpl
// Imports: Init.Prelude Init.Data.List.Basic
use crate::r#gen::Init::Data::List::Basic::{
    initialize_Init_Data_List_Basic, runtime_initialize_Init_Data_List_Basic,
};
use crate::r#gen::Init::Prelude::{
    initialize_Init_Prelude, l_List_lengthTR___redArg, runtime_initialize_Init_Prelude,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_List_toArrayAux___redArg(
    mut v_x_20_: *mut LeanObject,
    mut v_x_21_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_22_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_23_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_24_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_20_) == 0 {
                    return v_x_21_;
                } else {
                    v_head_22_ = lean_ctor_get(v_x_20_, 0);
                    lean_inc(v_head_22_);
                    v_tail_23_ = lean_ctor_get(v_x_20_, 1);
                    lean_inc(v_tail_23_);
                    lean_dec_ref_known(v_x_20_, 2);
                    v___x_24_ = lean_array_push(v_x_21_, v_head_22_);
                    v_x_20_ = v_tail_23_;
                    v_x_21_ = v___x_24_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_toArrayAux(
    mut v_00_u03b1_26_: *mut LeanObject,
    mut v_x_27_: *mut LeanObject,
    mut v_x_28_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_29_: *mut LeanObject = core::ptr::null_mut();
    v___x_29_ = l_List_toArrayAux___redArg(v_x_27_, v_x_28_);
    return v___x_29_;
}
pub unsafe fn l_List_toArrayImpl___redArg(mut v_xs_30_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_31_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut LeanObject = core::ptr::null_mut();
    v___x_31_ = l_List_lengthTR___redArg(v_xs_30_);
    v___x_32_ = lean_mk_empty_array_with_capacity(v___x_31_);
    lean_dec(v___x_31_);
    v___x_33_ = l_List_toArrayAux___redArg(v_xs_30_, v___x_32_);
    return v___x_33_;
}
pub unsafe fn lean_list_to_array(
    mut v_00_u03b1_34_: *mut LeanObject,
    mut v_xs_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
    v___x_36_ = l_List_lengthTR___redArg(v_xs_35_);
    v___x_37_ = lean_mk_empty_array_with_capacity(v___x_36_);
    lean_dec(v___x_36_);
    v___x_38_ = l_List_toArrayAux___redArg(v_xs_35_, v___x_37_);
    return v___x_38_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_ToArrayImpl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_ToArrayImpl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_ToArrayImpl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArrayImpl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_ToArrayImpl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_ToArrayImpl(builtin);
}

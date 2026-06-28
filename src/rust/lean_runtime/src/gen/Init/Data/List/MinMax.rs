// Lean compiler output
// Module: Init.Data.List.MinMax
// Imports: Init.Data.Subtype.Order Init.Data.Order.Lemmas Init.Data.List.Attach Init.Data.Bool Init.Data.List.Pairwise Init.Data.List.Sublist Init.Data.Option.Lemmas Init.Data.Subtype.Basic
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Attach::{
    initialize_Init_Data_List_Attach, runtime_initialize_Init_Data_List_Attach,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::Subtype::Basic::{
    initialize_Init_Data_Subtype_Basic, runtime_initialize_Init_Data_Subtype_Basic,
};
use crate::r#gen::Init::Data::Subtype::Order::{
    initialize_Init_Data_Subtype_Order, runtime_initialize_Init_Data_Subtype_Order,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_32_: *mut LeanObject,
    mut v_h__1_33_: *mut LeanObject,
    mut v_h__2_34_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_32_) == 0 {
        let mut v___x_35_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_34_);
        v___x_35_ = lean_box(0);
        v___x_36_ = lean_apply_1(v_h__1_33_, v___x_35_);
        return v___x_36_;
    } else {
        let mut v_head_37_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_38_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_33_);
        v_head_37_ = lean_ctor_get(v_x_32_, 0);
        lean_inc(v_head_37_);
        v_tail_38_ = lean_ctor_get(v_x_32_, 1);
        lean_inc(v_tail_38_);
        lean_dec_ref_known(v_x_32_, 2);
        v___x_39_ = lean_apply_2(v_h__2_34_, v_head_37_, v_tail_38_);
        return v___x_39_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_40_: *mut LeanObject,
    mut v_motive_41_: *mut LeanObject,
    mut v_x_42_: *mut LeanObject,
    mut v_h__1_43_: *mut LeanObject,
    mut v_h__2_44_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_42_) == 0 {
        let mut v___x_45_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_44_);
        v___x_45_ = lean_box(0);
        v___x_46_ = lean_apply_1(v_h__1_43_, v___x_45_);
        return v___x_46_;
    } else {
        let mut v_head_47_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_48_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_43_);
        v_head_47_ = lean_ctor_get(v_x_42_, 0);
        lean_inc(v_head_47_);
        v_tail_48_ = lean_ctor_get(v_x_42_, 1);
        lean_inc(v_tail_48_);
        lean_dec_ref_known(v_x_42_, 2);
        v___x_49_ = lean_apply_2(v_h__2_44_, v_head_47_, v_tail_48_);
        return v___x_49_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMax_0__List_head_match__1_splitter___redArg(
    mut v_x_50_: *mut LeanObject,
    mut v_h__1_51_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_52_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_53_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut LeanObject = core::ptr::null_mut();
    v_head_52_ = lean_ctor_get(v_x_50_, 0);
    lean_inc(v_head_52_);
    v_tail_53_ = lean_ctor_get(v_x_50_, 1);
    lean_inc(v_tail_53_);
    lean_dec(v_x_50_);
    v___x_54_ = lean_apply_3(v_h__1_51_, v_head_52_, v_tail_53_, lean_box(0));
    return v___x_54_;
}
pub unsafe fn l___private_Init_Data_List_MinMax_0__List_head_match__1_splitter(
    mut v_00_u03b1_55_: *mut LeanObject,
    mut v_motive_56_: *mut LeanObject,
    mut v_x_57_: *mut LeanObject,
    mut v_x_58_: *mut LeanObject,
    mut v_h__1_59_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_60_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_61_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    v_head_60_ = lean_ctor_get(v_x_57_, 0);
    lean_inc(v_head_60_);
    v_tail_61_ = lean_ctor_get(v_x_57_, 1);
    lean_inc(v_tail_61_);
    lean_dec(v_x_57_);
    v___x_62_ = lean_apply_3(v_h__1_59_, v_head_60_, v_tail_61_, lean_box(0));
    return v___x_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_MinMax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Subtype_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_MinMax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_MinMax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Subtype_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_MinMax(builtin);
}

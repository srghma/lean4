// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Pred
// Imports: Init.Data.String.Pattern.Pred Init.Data.String.Lemmas.Pattern.Basic Init.Data.String.Slice Init.Data.String.Search Init.Data.String.Slice Init.Data.String.Pattern.Pred Init.Data.String.Search Init.Data.Option.Lemmas Init.Data.String.Lemmas.Basic Init.Data.String.Lemmas.Order Init.Data.Order.Lemmas Init.Data.String.OrderInstances Init.Data.String.Lemmas.Iterate Init.Omega Init.Data.String.Lemmas.FindPos
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::Iterate::{
    initialize_Init_Data_String_Lemmas_Iterate, runtime_initialize_Init_Data_String_Lemmas_Iterate,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::String::Pattern::Pred::{
    initialize_Init_Data_String_Pattern_Pred, runtime_initialize_Init_Data_String_Pattern_Pred,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_String_Slice_Pattern_Model_CharPred_instPatternModelForallCharBool(
    mut v_p_33_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_34_: *mut LeanObject = core::ptr::null_mut();
    v___x_34_ = lean_box(0);
    return v___x_34_;
}
pub unsafe fn l_String_Slice_Pattern_Model_CharPred_instPatternModelForallCharBool___boxed(
    mut v_p_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_36_: *mut LeanObject = core::ptr::null_mut();
    v_res_36_ = l_String_Slice_Pattern_Model_CharPred_instPatternModelForallCharBool(v_p_35_);
    lean_dec_ref(v_p_35_);
    return v_res_36_;
}
pub unsafe fn l_String_Slice_Pattern_Model_CharPred_Decidable_instPatternModelForallCharPropOfDecidablePred(
    mut v_p_37_: *mut LeanObject,
    mut v_inst_38_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
    v___x_39_ = lean_box(0);
    return v___x_39_;
}
pub unsafe fn l_String_Slice_Pattern_Model_CharPred_Decidable_instPatternModelForallCharPropOfDecidablePred___boxed(
    mut v_p_40_: *mut LeanObject,
    mut v_inst_41_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_42_: *mut LeanObject = core::ptr::null_mut();
    v_res_42_ = l_String_Slice_Pattern_Model_CharPred_Decidable_instPatternModelForallCharPropOfDecidablePred(v_p_40_, v_inst_41_);
    lean_dec_ref(v_inst_41_);
    return v_res_42_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(
    mut v_x_43_: *mut LeanObject,
    mut v_h__1_44_: *mut LeanObject,
    mut v_h__2_45_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_43_) == 0 {
        let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_47_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_44_);
        v___x_46_ = lean_box(0);
        v___x_47_ = lean_apply_1(v_h__2_45_, v___x_46_);
        return v___x_47_;
    } else {
        let mut v_val_48_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_45_);
        v_val_48_ = lean_ctor_get(v_x_43_, 0);
        lean_inc(v_val_48_);
        lean_dec_ref_known(v_x_43_, 1);
        v___x_49_ = lean_apply_1(v_h__1_44_, v_val_48_);
        return v___x_49_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter(
    mut v_s_50_: *mut LeanObject,
    mut v_motive_51_: *mut LeanObject,
    mut v_x_52_: *mut LeanObject,
    mut v_h__1_53_: *mut LeanObject,
    mut v_h__2_54_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_52_) == 0 {
        let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_56_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_53_);
        v___x_55_ = lean_box(0);
        v___x_56_ = lean_apply_1(v_h__2_54_, v___x_55_);
        return v___x_56_;
    } else {
        let mut v_val_57_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_58_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_54_);
        v_val_57_ = lean_ctor_get(v_x_52_, 0);
        lean_inc(v_val_57_);
        lean_dec_ref_known(v_x_52_, 1);
        v___x_58_ = lean_apply_1(v_h__1_53_, v_val_57_);
        return v___x_58_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(
    mut v_s_59_: *mut LeanObject,
    mut v_motive_60_: *mut LeanObject,
    mut v_x_61_: *mut LeanObject,
    mut v_h__1_62_: *mut LeanObject,
    mut v_h__2_63_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_64_: *mut LeanObject = core::ptr::null_mut();
    v_res_64_ = l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_59_, v_motive_60_, v_x_61_, v_h__1_62_, v_h__2_63_);
    lean_dec_ref(v_s_59_);
    return v_res_64_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
}

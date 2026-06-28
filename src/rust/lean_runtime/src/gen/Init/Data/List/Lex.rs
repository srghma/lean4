// Lean compiler output
// Module: Init.Data.List.Lex
// Imports: Init.Data.Order.Lemmas Init.Data.BEq Init.Data.Order.Classes Init.Ext Init.NotationExtra Init.ByCases Init.Data.Bool Init.Data.List.Nat.TakeDrop Init.Data.List.TakeDrop Init.Data.Nat.Lemmas Init.TacticsExtra
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::BEq::{initialize_Init_Data_BEq, runtime_initialize_Init_Data_BEq};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_4, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_List_instTransLt(
    mut v_00_u03b1_43_: *mut LeanObject,
    mut v_inst_44_: *mut LeanObject,
    mut v_inst_45_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
    v___x_46_ = lean_box(0);
    return v___x_46_;
}
pub unsafe fn l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT(
    mut v_00_u03b1_47_: *mut LeanObject,
    mut v_inst_48_: *mut LeanObject,
    mut v_inst_49_: *mut LeanObject,
    mut v_inst_50_: *mut LeanObject,
    mut v_inst_51_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
    v___x_52_ = lean_box(0);
    return v___x_52_;
}
pub unsafe fn l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter___redArg(
    mut v_l_u2081_53_: *mut LeanObject,
    mut v_l_u2082_54_: *mut LeanObject,
    mut v_h__1_55_: *mut LeanObject,
    mut v_h__2_56_: *mut LeanObject,
    mut v_h__3_57_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_u2081_53_) == 0 {
        lean_dec(v_h__3_57_);
        if lean_obj_tag(v_l_u2082_54_) == 0 {
            let mut v___x_58_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_55_);
            v___x_58_ = lean_apply_1(v_h__2_56_, v_l_u2082_54_);
            return v___x_58_;
        } else {
            let mut v_head_59_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_60_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_56_);
            v_head_59_ = lean_ctor_get(v_l_u2082_54_, 0);
            lean_inc(v_head_59_);
            v_tail_60_ = lean_ctor_get(v_l_u2082_54_, 1);
            lean_inc(v_tail_60_);
            lean_dec_ref_known(v_l_u2082_54_, 2);
            v___x_61_ = lean_apply_2(v_h__1_55_, v_head_59_, v_tail_60_);
            return v___x_61_;
        }
    } else {
        lean_dec(v_h__1_55_);
        if lean_obj_tag(v_l_u2082_54_) == 0 {
            let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_57_);
            v___x_62_ = lean_apply_1(v_h__2_56_, v_l_u2081_53_);
            return v___x_62_;
        } else {
            let mut v_head_63_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_64_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_65_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_66_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_56_);
            v_head_63_ = lean_ctor_get(v_l_u2081_53_, 0);
            lean_inc(v_head_63_);
            v_tail_64_ = lean_ctor_get(v_l_u2081_53_, 1);
            lean_inc(v_tail_64_);
            lean_dec_ref_known(v_l_u2081_53_, 2);
            v_head_65_ = lean_ctor_get(v_l_u2082_54_, 0);
            lean_inc(v_head_65_);
            v_tail_66_ = lean_ctor_get(v_l_u2082_54_, 1);
            lean_inc(v_tail_66_);
            lean_dec_ref_known(v_l_u2082_54_, 2);
            v___x_67_ = lean_apply_4(v_h__3_57_, v_head_63_, v_tail_64_, v_head_65_, v_tail_66_);
            return v___x_67_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter(
    mut v_00_u03b1_68_: *mut LeanObject,
    mut v_motive_69_: *mut LeanObject,
    mut v_l_u2081_70_: *mut LeanObject,
    mut v_l_u2082_71_: *mut LeanObject,
    mut v_h__1_72_: *mut LeanObject,
    mut v_h__2_73_: *mut LeanObject,
    mut v_h__3_74_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_u2081_70_) == 0 {
        lean_dec(v_h__3_74_);
        if lean_obj_tag(v_l_u2082_71_) == 0 {
            let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_72_);
            v___x_75_ = lean_apply_1(v_h__2_73_, v_l_u2082_71_);
            return v___x_75_;
        } else {
            let mut v_head_76_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_77_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_73_);
            v_head_76_ = lean_ctor_get(v_l_u2082_71_, 0);
            lean_inc(v_head_76_);
            v_tail_77_ = lean_ctor_get(v_l_u2082_71_, 1);
            lean_inc(v_tail_77_);
            lean_dec_ref_known(v_l_u2082_71_, 2);
            v___x_78_ = lean_apply_2(v_h__1_72_, v_head_76_, v_tail_77_);
            return v___x_78_;
        }
    } else {
        lean_dec(v_h__1_72_);
        if lean_obj_tag(v_l_u2082_71_) == 0 {
            let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_74_);
            v___x_79_ = lean_apply_1(v_h__2_73_, v_l_u2081_70_);
            return v___x_79_;
        } else {
            let mut v_head_80_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_81_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_82_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_83_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_73_);
            v_head_80_ = lean_ctor_get(v_l_u2081_70_, 0);
            lean_inc(v_head_80_);
            v_tail_81_ = lean_ctor_get(v_l_u2081_70_, 1);
            lean_inc(v_tail_81_);
            lean_dec_ref_known(v_l_u2081_70_, 2);
            v_head_82_ = lean_ctor_get(v_l_u2082_71_, 0);
            lean_inc(v_head_82_);
            v_tail_83_ = lean_ctor_get(v_l_u2082_71_, 1);
            lean_inc(v_tail_83_);
            lean_dec_ref_known(v_l_u2082_71_, 2);
            v___x_84_ = lean_apply_4(v_h__3_74_, v_head_80_, v_tail_81_, v_head_82_, v_tail_83_);
            return v___x_84_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Lex(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Lex(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Lex(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Lex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Lex(builtin);
}

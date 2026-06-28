// Lean compiler output
// Module: Init.Data.Array.Sort.Lemmas
// Imports: Init.Data.Array.Sort.Basic Init.Data.List.Sort.Basic Init.Data.Array.Perm Init.Data.Array.Sort.Basic Init.Data.List.Sort.Basic Init.Data.List.Sort.Lemmas Init.Data.Slice.Array.Lemmas Init.Data.Slice.List.Lemmas Init.Data.Array.Bootstrap Init.Data.Array.Lemmas Init.Data.Array.MapIdx Init.ByCases
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Array::MapIdx::{
    initialize_Init_Data_Array_MapIdx, runtime_initialize_Init_Data_Array_MapIdx,
};
use crate::r#gen::Init::Data::Array::Perm::{
    initialize_Init_Data_Array_Perm, runtime_initialize_Init_Data_Array_Perm,
};
use crate::r#gen::Init::Data::Array::Sort::Basic::{
    initialize_Init_Data_Array_Sort_Basic, runtime_initialize_Init_Data_Array_Sort_Basic,
};
use crate::r#gen::Init::Data::List::Sort::Basic::{
    initialize_Init_Data_List_Sort_Basic, runtime_initialize_Init_Data_List_Sort_Basic,
};
use crate::r#gen::Init::Data::List::Sort::Lemmas::{
    initialize_Init_Data_List_Sort_Lemmas, runtime_initialize_Init_Data_List_Sort_Lemmas,
};
use crate::r#gen::Init::Data::Slice::Array::Lemmas::{
    initialize_Init_Data_Slice_Array_Lemmas, runtime_initialize_Init_Data_Slice_Array_Lemmas,
};
use crate::r#gen::Init::Data::Slice::List::Lemmas::{
    initialize_Init_Data_Slice_List_Lemmas, runtime_initialize_Init_Data_Slice_List_Lemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_4, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Array_Sort_Lemmas_0__List_merge_match__1_splitter___redArg(
    mut v_xs_55_: *mut LeanObject,
    mut v_ys_56_: *mut LeanObject,
    mut v_h__1_57_: *mut LeanObject,
    mut v_h__2_58_: *mut LeanObject,
    mut v_h__3_59_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_55_) == 0 {
        let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_59_);
        lean_dec(v_h__2_58_);
        v___x_60_ = lean_apply_1(v_h__1_57_, v_ys_56_);
        return v___x_60_;
    } else {
        lean_dec(v_h__1_57_);
        if lean_obj_tag(v_ys_56_) == 0 {
            let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_59_);
            v___x_61_ = lean_apply_2(v_h__2_58_, v_xs_55_, lean_box(0));
            return v___x_61_;
        } else {
            let mut v_head_62_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_63_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_64_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_65_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_58_);
            v_head_62_ = lean_ctor_get(v_xs_55_, 0);
            lean_inc(v_head_62_);
            v_tail_63_ = lean_ctor_get(v_xs_55_, 1);
            lean_inc(v_tail_63_);
            lean_dec_ref_known(v_xs_55_, 2);
            v_head_64_ = lean_ctor_get(v_ys_56_, 0);
            lean_inc(v_head_64_);
            v_tail_65_ = lean_ctor_get(v_ys_56_, 1);
            lean_inc(v_tail_65_);
            lean_dec_ref_known(v_ys_56_, 2);
            v___x_66_ = lean_apply_4(v_h__3_59_, v_head_62_, v_tail_63_, v_head_64_, v_tail_65_);
            return v___x_66_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Sort_Lemmas_0__List_merge_match__1_splitter(
    mut v_00_u03b1_67_: *mut LeanObject,
    mut v_motive_68_: *mut LeanObject,
    mut v_xs_69_: *mut LeanObject,
    mut v_ys_70_: *mut LeanObject,
    mut v_h__1_71_: *mut LeanObject,
    mut v_h__2_72_: *mut LeanObject,
    mut v_h__3_73_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_69_) == 0 {
        let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_73_);
        lean_dec(v_h__2_72_);
        v___x_74_ = lean_apply_1(v_h__1_71_, v_ys_70_);
        return v___x_74_;
    } else {
        lean_dec(v_h__1_71_);
        if lean_obj_tag(v_ys_70_) == 0 {
            let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_73_);
            v___x_75_ = lean_apply_2(v_h__2_72_, v_xs_69_, lean_box(0));
            return v___x_75_;
        } else {
            let mut v_head_76_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_77_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_78_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_79_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_72_);
            v_head_76_ = lean_ctor_get(v_xs_69_, 0);
            lean_inc(v_head_76_);
            v_tail_77_ = lean_ctor_get(v_xs_69_, 1);
            lean_inc(v_tail_77_);
            lean_dec_ref_known(v_xs_69_, 2);
            v_head_78_ = lean_ctor_get(v_ys_70_, 0);
            lean_inc(v_head_78_);
            v_tail_79_ = lean_ctor_get(v_ys_70_, 1);
            lean_inc(v_tail_79_);
            lean_dec_ref_known(v_ys_70_, 2);
            v___x_80_ = lean_apply_4(v_h__3_73_, v_head_76_, v_tail_77_, v_head_78_, v_tail_79_);
            return v___x_80_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Sort_Lemmas_0__List_mergeSort_match__1_splitter___redArg(
    mut v_x_81_: *mut LeanObject,
    mut v_x_82_: *mut LeanObject,
    mut v_h__1_83_: *mut LeanObject,
    mut v_h__2_84_: *mut LeanObject,
    mut v_h__3_85_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_81_) == 0 {
        let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_85_);
        lean_dec(v_h__2_84_);
        v___x_86_ = lean_apply_1(v_h__1_83_, v_x_82_);
        return v___x_86_;
    } else {
        let mut v_tail_87_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_83_);
        v_tail_87_ = lean_ctor_get(v_x_81_, 1);
        if lean_obj_tag(v_tail_87_) == 0 {
            let mut v_head_88_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_85_);
            v_head_88_ = lean_ctor_get(v_x_81_, 0);
            lean_inc(v_head_88_);
            lean_dec_ref_known(v_x_81_, 2);
            v___x_89_ = lean_apply_2(v_h__2_84_, v_head_88_, v_x_82_);
            return v___x_89_;
        } else {
            let mut v_head_90_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_91_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_92_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_87_);
            lean_dec(v_h__2_84_);
            v_head_90_ = lean_ctor_get(v_x_81_, 0);
            lean_inc(v_head_90_);
            lean_dec_ref_known(v_x_81_, 2);
            v_head_91_ = lean_ctor_get(v_tail_87_, 0);
            lean_inc(v_head_91_);
            v_tail_92_ = lean_ctor_get(v_tail_87_, 1);
            lean_inc(v_tail_92_);
            lean_dec_ref_known(v_tail_87_, 2);
            v___x_93_ = lean_apply_4(v_h__3_85_, v_head_90_, v_head_91_, v_tail_92_, v_x_82_);
            return v___x_93_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Sort_Lemmas_0__List_mergeSort_match__1_splitter(
    mut v_00_u03b1_94_: *mut LeanObject,
    mut v_motive_95_: *mut LeanObject,
    mut v_x_96_: *mut LeanObject,
    mut v_x_97_: *mut LeanObject,
    mut v_h__1_98_: *mut LeanObject,
    mut v_h__2_99_: *mut LeanObject,
    mut v_h__3_100_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_96_) == 0 {
        let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_100_);
        lean_dec(v_h__2_99_);
        v___x_101_ = lean_apply_1(v_h__1_98_, v_x_97_);
        return v___x_101_;
    } else {
        let mut v_tail_102_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_98_);
        v_tail_102_ = lean_ctor_get(v_x_96_, 1);
        if lean_obj_tag(v_tail_102_) == 0 {
            let mut v_head_103_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_100_);
            v_head_103_ = lean_ctor_get(v_x_96_, 0);
            lean_inc(v_head_103_);
            lean_dec_ref_known(v_x_96_, 2);
            v___x_104_ = lean_apply_2(v_h__2_99_, v_head_103_, v_x_97_);
            return v___x_104_;
        } else {
            let mut v_head_105_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_106_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_107_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_102_);
            lean_dec(v_h__2_99_);
            v_head_105_ = lean_ctor_get(v_x_96_, 0);
            lean_inc(v_head_105_);
            lean_dec_ref_known(v_x_96_, 2);
            v_head_106_ = lean_ctor_get(v_tail_102_, 0);
            lean_inc(v_head_106_);
            v_tail_107_ = lean_ctor_get(v_tail_102_, 1);
            lean_inc(v_tail_107_);
            lean_dec_ref_known(v_tail_102_, 2);
            v___x_108_ = lean_apply_4(v_h__3_100_, v_head_105_, v_head_106_, v_tail_107_, v_x_97_);
            return v___x_108_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Sort_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Sort_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Sort_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Sort_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Sort_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_Sort_Lemmas(builtin);
}

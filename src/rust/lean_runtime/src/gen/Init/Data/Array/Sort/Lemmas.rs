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
pub unsafe fn l___private_Init_Data_Array_Sort_Lemmas_0__List_merge_match__1_splitter___redArg(
    mut v_xs_55_: *mut crate::leanh::LeanObject,
    mut v_ys_56_: *mut crate::leanh::LeanObject,
    mut v_h__1_57_: *mut crate::leanh::LeanObject,
    mut v_h__2_58_: *mut crate::leanh::LeanObject,
    mut v_h__3_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_xs_55_) == 0 {
        let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_59_);
        crate::leanh::lean_dec(v_h__2_58_);
        v___x_60_ = crate::leanh::lean_apply_1(v_h__1_57_, v_ys_56_);
        return v___x_60_;
    } else {
        crate::leanh::lean_dec(v_h__1_57_);
        if crate::leanh::lean_obj_tag(v_ys_56_) == 0 {
            let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_59_);
            v___x_61_ = crate::leanh::lean_apply_2(v_h__2_58_, v_xs_55_, crate::leanh::lean_box(0));
            return v___x_61_;
        } else {
            let mut v_head_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_58_);
            v_head_62_ = crate::leanh::lean_ctor_get(v_xs_55_, 0);
            crate::leanh::lean_inc(v_head_62_);
            v_tail_63_ = crate::leanh::lean_ctor_get(v_xs_55_, 1);
            crate::leanh::lean_inc(v_tail_63_);
            crate::leanh::lean_dec_ref_known(v_xs_55_, 2);
            v_head_64_ = crate::leanh::lean_ctor_get(v_ys_56_, 0);
            crate::leanh::lean_inc(v_head_64_);
            v_tail_65_ = crate::leanh::lean_ctor_get(v_ys_56_, 1);
            crate::leanh::lean_inc(v_tail_65_);
            crate::leanh::lean_dec_ref_known(v_ys_56_, 2);
            v___x_66_ = crate::leanh::lean_apply_4(
                v_h__3_59_, v_head_62_, v_tail_63_, v_head_64_, v_tail_65_,
            );
            return v___x_66_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Sort_Lemmas_0__List_merge_match__1_splitter(
    mut v_00_u03b1_67_: *mut crate::leanh::LeanObject,
    mut v_motive_68_: *mut crate::leanh::LeanObject,
    mut v_xs_69_: *mut crate::leanh::LeanObject,
    mut v_ys_70_: *mut crate::leanh::LeanObject,
    mut v_h__1_71_: *mut crate::leanh::LeanObject,
    mut v_h__2_72_: *mut crate::leanh::LeanObject,
    mut v_h__3_73_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_xs_69_) == 0 {
        let mut v___x_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_73_);
        crate::leanh::lean_dec(v_h__2_72_);
        v___x_74_ = crate::leanh::lean_apply_1(v_h__1_71_, v_ys_70_);
        return v___x_74_;
    } else {
        crate::leanh::lean_dec(v_h__1_71_);
        if crate::leanh::lean_obj_tag(v_ys_70_) == 0 {
            let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_73_);
            v___x_75_ = crate::leanh::lean_apply_2(v_h__2_72_, v_xs_69_, crate::leanh::lean_box(0));
            return v___x_75_;
        } else {
            let mut v_head_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_72_);
            v_head_76_ = crate::leanh::lean_ctor_get(v_xs_69_, 0);
            crate::leanh::lean_inc(v_head_76_);
            v_tail_77_ = crate::leanh::lean_ctor_get(v_xs_69_, 1);
            crate::leanh::lean_inc(v_tail_77_);
            crate::leanh::lean_dec_ref_known(v_xs_69_, 2);
            v_head_78_ = crate::leanh::lean_ctor_get(v_ys_70_, 0);
            crate::leanh::lean_inc(v_head_78_);
            v_tail_79_ = crate::leanh::lean_ctor_get(v_ys_70_, 1);
            crate::leanh::lean_inc(v_tail_79_);
            crate::leanh::lean_dec_ref_known(v_ys_70_, 2);
            v___x_80_ = crate::leanh::lean_apply_4(
                v_h__3_73_, v_head_76_, v_tail_77_, v_head_78_, v_tail_79_,
            );
            return v___x_80_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Sort_Lemmas_0__List_mergeSort_match__1_splitter___redArg(
    mut v_x_81_: *mut crate::leanh::LeanObject,
    mut v_x_82_: *mut crate::leanh::LeanObject,
    mut v_h__1_83_: *mut crate::leanh::LeanObject,
    mut v_h__2_84_: *mut crate::leanh::LeanObject,
    mut v_h__3_85_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_81_) == 0 {
        let mut v___x_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_85_);
        crate::leanh::lean_dec(v_h__2_84_);
        v___x_86_ = crate::leanh::lean_apply_1(v_h__1_83_, v_x_82_);
        return v___x_86_;
    } else {
        let mut v_tail_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_83_);
        v_tail_87_ = crate::leanh::lean_ctor_get(v_x_81_, 1);
        if crate::leanh::lean_obj_tag(v_tail_87_) == 0 {
            let mut v_head_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_85_);
            v_head_88_ = crate::leanh::lean_ctor_get(v_x_81_, 0);
            crate::leanh::lean_inc(v_head_88_);
            crate::leanh::lean_dec_ref_known(v_x_81_, 2);
            v___x_89_ = crate::leanh::lean_apply_2(v_h__2_84_, v_head_88_, v_x_82_);
            return v___x_89_;
        } else {
            let mut v_head_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_87_);
            crate::leanh::lean_dec(v_h__2_84_);
            v_head_90_ = crate::leanh::lean_ctor_get(v_x_81_, 0);
            crate::leanh::lean_inc(v_head_90_);
            crate::leanh::lean_dec_ref_known(v_x_81_, 2);
            v_head_91_ = crate::leanh::lean_ctor_get(v_tail_87_, 0);
            crate::leanh::lean_inc(v_head_91_);
            v_tail_92_ = crate::leanh::lean_ctor_get(v_tail_87_, 1);
            crate::leanh::lean_inc(v_tail_92_);
            crate::leanh::lean_dec_ref_known(v_tail_87_, 2);
            v___x_93_ =
                crate::leanh::lean_apply_4(v_h__3_85_, v_head_90_, v_head_91_, v_tail_92_, v_x_82_);
            return v___x_93_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Sort_Lemmas_0__List_mergeSort_match__1_splitter(
    mut v_00_u03b1_94_: *mut crate::leanh::LeanObject,
    mut v_motive_95_: *mut crate::leanh::LeanObject,
    mut v_x_96_: *mut crate::leanh::LeanObject,
    mut v_x_97_: *mut crate::leanh::LeanObject,
    mut v_h__1_98_: *mut crate::leanh::LeanObject,
    mut v_h__2_99_: *mut crate::leanh::LeanObject,
    mut v_h__3_100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_96_) == 0 {
        let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_100_);
        crate::leanh::lean_dec(v_h__2_99_);
        v___x_101_ = crate::leanh::lean_apply_1(v_h__1_98_, v_x_97_);
        return v___x_101_;
    } else {
        let mut v_tail_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_98_);
        v_tail_102_ = crate::leanh::lean_ctor_get(v_x_96_, 1);
        if crate::leanh::lean_obj_tag(v_tail_102_) == 0 {
            let mut v_head_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_100_);
            v_head_103_ = crate::leanh::lean_ctor_get(v_x_96_, 0);
            crate::leanh::lean_inc(v_head_103_);
            crate::leanh::lean_dec_ref_known(v_x_96_, 2);
            v___x_104_ = crate::leanh::lean_apply_2(v_h__2_99_, v_head_103_, v_x_97_);
            return v___x_104_;
        } else {
            let mut v_head_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_102_);
            crate::leanh::lean_dec(v_h__2_99_);
            v_head_105_ = crate::leanh::lean_ctor_get(v_x_96_, 0);
            crate::leanh::lean_inc(v_head_105_);
            crate::leanh::lean_dec_ref_known(v_x_96_, 2);
            v_head_106_ = crate::leanh::lean_ctor_get(v_tail_102_, 0);
            crate::leanh::lean_inc(v_head_106_);
            v_tail_107_ = crate::leanh::lean_ctor_get(v_tail_102_, 1);
            crate::leanh::lean_inc(v_tail_107_);
            crate::leanh::lean_dec_ref_known(v_tail_102_, 2);
            v___x_108_ = crate::leanh::lean_apply_4(
                v_h__3_100_,
                v_head_105_,
                v_head_106_,
                v_tail_107_,
                v_x_97_,
            );
            return v___x_108_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Sort_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Sort_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Sort_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Sort_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Sort_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Sort_Lemmas(builtin);
}

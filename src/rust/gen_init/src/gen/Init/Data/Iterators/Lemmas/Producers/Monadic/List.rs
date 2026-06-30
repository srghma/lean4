// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Producers.Monadic.List
// Imports: Init.Data.Iterators.Producers.Monadic.List Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.List.ToArray
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Producers::Monadic::List::{
    initialize_Init_Data_Iterators_Producers_Monadic_List,
    runtime_initialize_Init_Data_Iterators_Producers_Monadic_List,
};
use crate::r#gen::Init::Data::List::ToArray::{
    initialize_Init_Data_List_ToArray, runtime_initialize_Init_Data_List_ToArray,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(
    mut v_it_46_: *mut leanh::LeanObject,
    mut v_h__1_47_: *mut leanh::LeanObject,
    mut v_h__2_48_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_46_) == 0 {
        let mut v___x_49_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_48_);
        v___x_49_ = leanh::lean_box(0);
        v___x_50_ = leanh::lean_apply_1(v_h__1_47_, v___x_49_);
        return v___x_50_;
    } else {
        let mut v_head_51_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_52_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_53_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_47_);
        v_head_51_ = leanh::lean_ctor_get(v_it_46_, 0);
        leanh::lean_inc(v_head_51_);
        v_tail_52_ = leanh::lean_ctor_get(v_it_46_, 1);
        leanh::lean_inc(v_tail_52_);
        leanh::lean_dec_ref_known(v_it_46_, 2);
        v___x_53_ = leanh::lean_apply_2(v_h__2_48_, v_head_51_, v_tail_52_);
        return v___x_53_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(
    mut v_m_54_: *mut leanh::LeanObject,
    mut v_00_u03b1_55_: *mut leanh::LeanObject,
    mut v_motive_56_: *mut leanh::LeanObject,
    mut v_it_57_: *mut leanh::LeanObject,
    mut v_h__1_58_: *mut leanh::LeanObject,
    mut v_h__2_59_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_57_) == 0 {
        let mut v___x_60_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_59_);
        v___x_60_ = leanh::lean_box(0);
        v___x_61_ = leanh::lean_apply_1(v_h__1_58_, v___x_60_);
        return v___x_61_;
    } else {
        let mut v_head_62_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_63_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_58_);
        v_head_62_ = leanh::lean_ctor_get(v_it_57_, 0);
        leanh::lean_inc(v_head_62_);
        v_tail_63_ = leanh::lean_ctor_get(v_it_57_, 1);
        leanh::lean_inc(v_tail_63_);
        leanh::lean_dec_ref_known(v_it_57_, 2);
        v___x_64_ = leanh::lean_apply_2(v_h__2_59_, v_head_62_, v_tail_63_);
        return v___x_64_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_65_: *mut leanh::LeanObject,
    mut v_h__1_66_: *mut leanh::LeanObject,
    mut v_h__2_67_: *mut leanh::LeanObject,
    mut v_h__3_68_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_65_) {
        0 => {
            let mut v_it_69_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_70_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_71_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_68_);
            leanh::lean_dec(v_h__2_67_);
            v_it_69_ = leanh::lean_ctor_get(v_x_65_, 0);
            leanh::lean_inc(v_it_69_);
            v_out_70_ = leanh::lean_ctor_get(v_x_65_, 1);
            leanh::lean_inc(v_out_70_);
            leanh::lean_dec_ref_known(v_x_65_, 2);
            v___x_71_ = leanh::lean_apply_2(v_h__1_66_, v_it_69_, v_out_70_);
            return v___x_71_;
        }
        1 => {
            let mut v_it_72_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_73_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_68_);
            leanh::lean_dec(v_h__1_66_);
            v_it_72_ = leanh::lean_ctor_get(v_x_65_, 0);
            leanh::lean_inc(v_it_72_);
            leanh::lean_dec_ref_known(v_x_65_, 1);
            v___x_73_ = leanh::lean_apply_1(v_h__2_67_, v_it_72_);
            return v___x_73_;
        }
        _ => {
            let mut v___x_74_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_75_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_67_);
            leanh::lean_dec(v_h__1_66_);
            v___x_74_ = leanh::lean_box(0);
            v___x_75_ = leanh::lean_apply_1(v_h__3_68_, v___x_74_);
            return v___x_75_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_76_: *mut leanh::LeanObject,
    mut v_00_u03b2_77_: *mut leanh::LeanObject,
    mut v_m_78_: *mut leanh::LeanObject,
    mut v_motive_79_: *mut leanh::LeanObject,
    mut v_x_80_: *mut leanh::LeanObject,
    mut v_h__1_81_: *mut leanh::LeanObject,
    mut v_h__2_82_: *mut leanh::LeanObject,
    mut v_h__3_83_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_80_) {
        0 => {
            let mut v_it_84_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_85_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_86_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_83_);
            leanh::lean_dec(v_h__2_82_);
            v_it_84_ = leanh::lean_ctor_get(v_x_80_, 0);
            leanh::lean_inc(v_it_84_);
            v_out_85_ = leanh::lean_ctor_get(v_x_80_, 1);
            leanh::lean_inc(v_out_85_);
            leanh::lean_dec_ref_known(v_x_80_, 2);
            v___x_86_ = leanh::lean_apply_2(v_h__1_81_, v_it_84_, v_out_85_);
            return v___x_86_;
        }
        1 => {
            let mut v_it_87_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_83_);
            leanh::lean_dec(v_h__1_81_);
            v_it_87_ = leanh::lean_ctor_get(v_x_80_, 0);
            leanh::lean_inc(v_it_87_);
            leanh::lean_dec_ref_known(v_x_80_, 1);
            v___x_88_ = leanh::lean_apply_1(v_h__2_82_, v_it_87_);
            return v___x_88_;
        }
        _ => {
            let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_90_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_82_);
            leanh::lean_dec(v_h__1_81_);
            v___x_89_ = leanh::lean_box(0);
            v___x_90_ = leanh::lean_apply_1(v_h__3_83_, v___x_89_);
            return v___x_90_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_ToArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
}
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
    mut v_it_46_: *mut crate::leanh::LeanObject,
    mut v_h__1_47_: *mut crate::leanh::LeanObject,
    mut v_h__2_48_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_46_) == 0 {
        let mut v___x_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_48_);
        v___x_49_ = crate::leanh::lean_box(0);
        v___x_50_ = crate::leanh::lean_apply_1(v_h__1_47_, v___x_49_);
        return v___x_50_;
    } else {
        let mut v_head_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_47_);
        v_head_51_ = crate::leanh::lean_ctor_get(v_it_46_, 0);
        crate::leanh::lean_inc(v_head_51_);
        v_tail_52_ = crate::leanh::lean_ctor_get(v_it_46_, 1);
        crate::leanh::lean_inc(v_tail_52_);
        crate::leanh::lean_dec_ref_known(v_it_46_, 2);
        v___x_53_ = crate::leanh::lean_apply_2(v_h__2_48_, v_head_51_, v_tail_52_);
        return v___x_53_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(
    mut v_m_54_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_55_: *mut crate::leanh::LeanObject,
    mut v_motive_56_: *mut crate::leanh::LeanObject,
    mut v_it_57_: *mut crate::leanh::LeanObject,
    mut v_h__1_58_: *mut crate::leanh::LeanObject,
    mut v_h__2_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_57_) == 0 {
        let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_59_);
        v___x_60_ = crate::leanh::lean_box(0);
        v___x_61_ = crate::leanh::lean_apply_1(v_h__1_58_, v___x_60_);
        return v___x_61_;
    } else {
        let mut v_head_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_58_);
        v_head_62_ = crate::leanh::lean_ctor_get(v_it_57_, 0);
        crate::leanh::lean_inc(v_head_62_);
        v_tail_63_ = crate::leanh::lean_ctor_get(v_it_57_, 1);
        crate::leanh::lean_inc(v_tail_63_);
        crate::leanh::lean_dec_ref_known(v_it_57_, 2);
        v___x_64_ = crate::leanh::lean_apply_2(v_h__2_59_, v_head_62_, v_tail_63_);
        return v___x_64_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_65_: *mut crate::leanh::LeanObject,
    mut v_h__1_66_: *mut crate::leanh::LeanObject,
    mut v_h__2_67_: *mut crate::leanh::LeanObject,
    mut v_h__3_68_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_65_) {
        0 => {
            let mut v_it_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_68_);
            crate::leanh::lean_dec(v_h__2_67_);
            v_it_69_ = crate::leanh::lean_ctor_get(v_x_65_, 0);
            crate::leanh::lean_inc(v_it_69_);
            v_out_70_ = crate::leanh::lean_ctor_get(v_x_65_, 1);
            crate::leanh::lean_inc(v_out_70_);
            crate::leanh::lean_dec_ref_known(v_x_65_, 2);
            v___x_71_ = crate::leanh::lean_apply_2(v_h__1_66_, v_it_69_, v_out_70_);
            return v___x_71_;
        }
        1 => {
            let mut v_it_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_68_);
            crate::leanh::lean_dec(v_h__1_66_);
            v_it_72_ = crate::leanh::lean_ctor_get(v_x_65_, 0);
            crate::leanh::lean_inc(v_it_72_);
            crate::leanh::lean_dec_ref_known(v_x_65_, 1);
            v___x_73_ = crate::leanh::lean_apply_1(v_h__2_67_, v_it_72_);
            return v___x_73_;
        }
        _ => {
            let mut v___x_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_67_);
            crate::leanh::lean_dec(v_h__1_66_);
            v___x_74_ = crate::leanh::lean_box(0);
            v___x_75_ = crate::leanh::lean_apply_1(v_h__3_68_, v___x_74_);
            return v___x_75_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_76_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_77_: *mut crate::leanh::LeanObject,
    mut v_m_78_: *mut crate::leanh::LeanObject,
    mut v_motive_79_: *mut crate::leanh::LeanObject,
    mut v_x_80_: *mut crate::leanh::LeanObject,
    mut v_h__1_81_: *mut crate::leanh::LeanObject,
    mut v_h__2_82_: *mut crate::leanh::LeanObject,
    mut v_h__3_83_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_80_) {
        0 => {
            let mut v_it_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_83_);
            crate::leanh::lean_dec(v_h__2_82_);
            v_it_84_ = crate::leanh::lean_ctor_get(v_x_80_, 0);
            crate::leanh::lean_inc(v_it_84_);
            v_out_85_ = crate::leanh::lean_ctor_get(v_x_80_, 1);
            crate::leanh::lean_inc(v_out_85_);
            crate::leanh::lean_dec_ref_known(v_x_80_, 2);
            v___x_86_ = crate::leanh::lean_apply_2(v_h__1_81_, v_it_84_, v_out_85_);
            return v___x_86_;
        }
        1 => {
            let mut v_it_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_83_);
            crate::leanh::lean_dec(v_h__1_81_);
            v_it_87_ = crate::leanh::lean_ctor_get(v_x_80_, 0);
            crate::leanh::lean_inc(v_it_87_);
            crate::leanh::lean_dec_ref_known(v_x_80_, 1);
            v___x_88_ = crate::leanh::lean_apply_1(v_h__2_82_, v_it_87_);
            return v___x_88_;
        }
        _ => {
            let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_82_);
            crate::leanh::lean_dec(v_h__1_81_);
            v___x_89_ = crate::leanh::lean_box(0);
            v___x_90_ = crate::leanh::lean_apply_1(v_h__3_83_, v___x_89_);
            return v___x_90_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_ToArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
}

// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Monadic.List
// Imports: Init.Data.Iterators.Lemmas.Producers.Monadic.List Std.Data.Iterators.Lemmas.Equivalence.Basic
use crate::r#gen::Init::Data::Iterators::Lemmas::Producers::Monadic::List::{
    initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List,
    runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Equivalence::Basic::{
    initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic,
    runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter___redArg(
    mut v_l_63_: *mut leanh::LeanObject,
    mut v_h__1_64_: *mut leanh::LeanObject,
    mut v_h__2_65_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_63_) == 0 {
        let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_67_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_65_);
        v___x_66_ = leanh::lean_box(0);
        v___x_67_ = leanh::lean_apply_1(v_h__1_64_, v___x_66_);
        return v___x_67_;
    } else {
        let mut v_head_68_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_69_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_70_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_64_);
        v_head_68_ = leanh::lean_ctor_get(v_l_63_, 0);
        leanh::lean_inc(v_head_68_);
        v_tail_69_ = leanh::lean_ctor_get(v_l_63_, 1);
        leanh::lean_inc(v_tail_69_);
        leanh::lean_dec_ref_known(v_l_63_, 2);
        v___x_70_ = leanh::lean_apply_2(v_h__2_65_, v_head_68_, v_tail_69_);
        return v___x_70_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter(
    mut v_00_u03b2_71_: *mut leanh::LeanObject,
    mut v_motive_72_: *mut leanh::LeanObject,
    mut v_l_73_: *mut leanh::LeanObject,
    mut v_h__1_74_: *mut leanh::LeanObject,
    mut v_h__2_75_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_73_) == 0 {
        let mut v___x_76_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_77_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_75_);
        v___x_76_ = leanh::lean_box(0);
        v___x_77_ = leanh::lean_apply_1(v_h__1_74_, v___x_76_);
        return v___x_77_;
    } else {
        let mut v_head_78_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_79_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_80_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_74_);
        v_head_78_ = leanh::lean_ctor_get(v_l_73_, 0);
        leanh::lean_inc(v_head_78_);
        v_tail_79_ = leanh::lean_ctor_get(v_l_73_, 1);
        leanh::lean_inc(v_tail_79_);
        leanh::lean_dec_ref_known(v_l_73_, 2);
        v___x_80_ = leanh::lean_apply_2(v_h__2_75_, v_head_78_, v_tail_79_);
        return v___x_80_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(
    mut v_it_81_: *mut leanh::LeanObject,
    mut v_h__1_82_: *mut leanh::LeanObject,
    mut v_h__2_83_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_81_) == 0 {
        let mut v___x_84_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_85_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_83_);
        v___x_84_ = leanh::lean_box(0);
        v___x_85_ = leanh::lean_apply_1(v_h__1_82_, v___x_84_);
        return v___x_85_;
    } else {
        let mut v_head_86_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_87_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_82_);
        v_head_86_ = leanh::lean_ctor_get(v_it_81_, 0);
        leanh::lean_inc(v_head_86_);
        v_tail_87_ = leanh::lean_ctor_get(v_it_81_, 1);
        leanh::lean_inc(v_tail_87_);
        leanh::lean_dec_ref_known(v_it_81_, 2);
        v___x_88_ = leanh::lean_apply_2(v_h__2_83_, v_head_86_, v_tail_87_);
        return v___x_88_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(
    mut v_m_89_: *mut leanh::LeanObject,
    mut v_00_u03b1_90_: *mut leanh::LeanObject,
    mut v_motive_91_: *mut leanh::LeanObject,
    mut v_it_92_: *mut leanh::LeanObject,
    mut v_h__1_93_: *mut leanh::LeanObject,
    mut v_h__2_94_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_92_) == 0 {
        let mut v___x_95_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_94_);
        v___x_95_ = leanh::lean_box(0);
        v___x_96_ = leanh::lean_apply_1(v_h__1_93_, v___x_95_);
        return v___x_96_;
    } else {
        let mut v_head_97_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_98_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_93_);
        v_head_97_ = leanh::lean_ctor_get(v_it_92_, 0);
        leanh::lean_inc(v_head_97_);
        v_tail_98_ = leanh::lean_ctor_get(v_it_92_, 1);
        leanh::lean_inc(v_tail_98_);
        leanh::lean_dec_ref_known(v_it_92_, 2);
        v___x_99_ = leanh::lean_apply_2(v_h__2_94_, v_head_97_, v_tail_98_);
        return v___x_99_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(
    mut v_x_100_: *mut leanh::LeanObject,
    mut v_h__1_101_: *mut leanh::LeanObject,
    mut v_h__2_102_: *mut leanh::LeanObject,
    mut v_h__3_103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_100_) {
        0 => {
            let mut v_it_104_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_105_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_103_);
            leanh::lean_dec(v_h__2_102_);
            v_it_104_ = leanh::lean_ctor_get(v_x_100_, 0);
            leanh::lean_inc(v_it_104_);
            v_out_105_ = leanh::lean_ctor_get(v_x_100_, 1);
            leanh::lean_inc(v_out_105_);
            leanh::lean_dec_ref_known(v_x_100_, 2);
            v___x_106_ = leanh::lean_apply_2(v_h__1_101_, v_it_104_, v_out_105_);
            return v___x_106_;
        }
        1 => {
            let mut v_it_107_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_103_);
            leanh::lean_dec(v_h__1_101_);
            v_it_107_ = leanh::lean_ctor_get(v_x_100_, 0);
            leanh::lean_inc(v_it_107_);
            leanh::lean_dec_ref_known(v_x_100_, 1);
            v___x_108_ = leanh::lean_apply_1(v_h__2_102_, v_it_107_);
            return v___x_108_;
        }
        _ => {
            let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_102_);
            leanh::lean_dec(v_h__1_101_);
            v___x_109_ = leanh::lean_box(0);
            v___x_110_ = leanh::lean_apply_1(v_h__3_103_, v___x_109_);
            return v___x_110_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter(
    mut v_m_111_: *mut leanh::LeanObject,
    mut v_00_u03b1_112_: *mut leanh::LeanObject,
    mut v_motive_113_: *mut leanh::LeanObject,
    mut v_x_114_: *mut leanh::LeanObject,
    mut v_h__1_115_: *mut leanh::LeanObject,
    mut v_h__2_116_: *mut leanh::LeanObject,
    mut v_h__3_117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_114_) {
        0 => {
            let mut v_it_118_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_119_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_117_);
            leanh::lean_dec(v_h__2_116_);
            v_it_118_ = leanh::lean_ctor_get(v_x_114_, 0);
            leanh::lean_inc(v_it_118_);
            v_out_119_ = leanh::lean_ctor_get(v_x_114_, 1);
            leanh::lean_inc(v_out_119_);
            leanh::lean_dec_ref_known(v_x_114_, 2);
            v___x_120_ = leanh::lean_apply_2(v_h__1_115_, v_it_118_, v_out_119_);
            return v___x_120_;
        }
        1 => {
            let mut v_it_121_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_117_);
            leanh::lean_dec(v_h__1_115_);
            v_it_121_ = leanh::lean_ctor_get(v_x_114_, 0);
            leanh::lean_inc(v_it_121_);
            leanh::lean_dec_ref_known(v_x_114_, 1);
            v___x_122_ = leanh::lean_apply_1(v_h__2_116_, v_it_121_);
            return v___x_122_;
        }
        _ => {
            let mut v___x_123_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_116_);
            leanh::lean_dec(v_h__1_115_);
            v___x_123_ = leanh::lean_box(0);
            v___x_124_ = leanh::lean_apply_1(v_h__3_117_, v___x_123_);
            return v___x_124_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
}
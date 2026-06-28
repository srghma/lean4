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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter___redArg(
    mut v_l_63_: *mut LeanObject,
    mut v_h__1_64_: *mut LeanObject,
    mut v_h__2_65_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_63_) == 0 {
        let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_65_);
        v___x_66_ = lean_box(0);
        v___x_67_ = lean_apply_1(v_h__1_64_, v___x_66_);
        return v___x_67_;
    } else {
        let mut v_head_68_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_69_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_64_);
        v_head_68_ = lean_ctor_get(v_l_63_, 0);
        lean_inc(v_head_68_);
        v_tail_69_ = lean_ctor_get(v_l_63_, 1);
        lean_inc(v_tail_69_);
        lean_dec_ref_known(v_l_63_, 2);
        v___x_70_ = lean_apply_2(v_h__2_65_, v_head_68_, v_tail_69_);
        return v___x_70_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter(
    mut v_00_u03b2_71_: *mut LeanObject,
    mut v_motive_72_: *mut LeanObject,
    mut v_l_73_: *mut LeanObject,
    mut v_h__1_74_: *mut LeanObject,
    mut v_h__2_75_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_73_) == 0 {
        let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_75_);
        v___x_76_ = lean_box(0);
        v___x_77_ = lean_apply_1(v_h__1_74_, v___x_76_);
        return v___x_77_;
    } else {
        let mut v_head_78_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_79_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_74_);
        v_head_78_ = lean_ctor_get(v_l_73_, 0);
        lean_inc(v_head_78_);
        v_tail_79_ = lean_ctor_get(v_l_73_, 1);
        lean_inc(v_tail_79_);
        lean_dec_ref_known(v_l_73_, 2);
        v___x_80_ = lean_apply_2(v_h__2_75_, v_head_78_, v_tail_79_);
        return v___x_80_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(
    mut v_it_81_: *mut LeanObject,
    mut v_h__1_82_: *mut LeanObject,
    mut v_h__2_83_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_81_) == 0 {
        let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_83_);
        v___x_84_ = lean_box(0);
        v___x_85_ = lean_apply_1(v_h__1_82_, v___x_84_);
        return v___x_85_;
    } else {
        let mut v_head_86_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_87_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_82_);
        v_head_86_ = lean_ctor_get(v_it_81_, 0);
        lean_inc(v_head_86_);
        v_tail_87_ = lean_ctor_get(v_it_81_, 1);
        lean_inc(v_tail_87_);
        lean_dec_ref_known(v_it_81_, 2);
        v___x_88_ = lean_apply_2(v_h__2_83_, v_head_86_, v_tail_87_);
        return v___x_88_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(
    mut v_m_89_: *mut LeanObject,
    mut v_00_u03b1_90_: *mut LeanObject,
    mut v_motive_91_: *mut LeanObject,
    mut v_it_92_: *mut LeanObject,
    mut v_h__1_93_: *mut LeanObject,
    mut v_h__2_94_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_92_) == 0 {
        let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_94_);
        v___x_95_ = lean_box(0);
        v___x_96_ = lean_apply_1(v_h__1_93_, v___x_95_);
        return v___x_96_;
    } else {
        let mut v_head_97_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_98_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_93_);
        v_head_97_ = lean_ctor_get(v_it_92_, 0);
        lean_inc(v_head_97_);
        v_tail_98_ = lean_ctor_get(v_it_92_, 1);
        lean_inc(v_tail_98_);
        lean_dec_ref_known(v_it_92_, 2);
        v___x_99_ = lean_apply_2(v_h__2_94_, v_head_97_, v_tail_98_);
        return v___x_99_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(
    mut v_x_100_: *mut LeanObject,
    mut v_h__1_101_: *mut LeanObject,
    mut v_h__2_102_: *mut LeanObject,
    mut v_h__3_103_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_100_) {
        0 => {
            let mut v_it_104_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_105_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_103_);
            lean_dec(v_h__2_102_);
            v_it_104_ = lean_ctor_get(v_x_100_, 0);
            lean_inc(v_it_104_);
            v_out_105_ = lean_ctor_get(v_x_100_, 1);
            lean_inc(v_out_105_);
            lean_dec_ref_known(v_x_100_, 2);
            v___x_106_ = lean_apply_2(v_h__1_101_, v_it_104_, v_out_105_);
            return v___x_106_;
        }
        1 => {
            let mut v_it_107_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_103_);
            lean_dec(v_h__1_101_);
            v_it_107_ = lean_ctor_get(v_x_100_, 0);
            lean_inc(v_it_107_);
            lean_dec_ref_known(v_x_100_, 1);
            v___x_108_ = lean_apply_1(v_h__2_102_, v_it_107_);
            return v___x_108_;
        }
        _ => {
            let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_102_);
            lean_dec(v_h__1_101_);
            v___x_109_ = lean_box(0);
            v___x_110_ = lean_apply_1(v_h__3_103_, v___x_109_);
            return v___x_110_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter(
    mut v_m_111_: *mut LeanObject,
    mut v_00_u03b1_112_: *mut LeanObject,
    mut v_motive_113_: *mut LeanObject,
    mut v_x_114_: *mut LeanObject,
    mut v_h__1_115_: *mut LeanObject,
    mut v_h__2_116_: *mut LeanObject,
    mut v_h__3_117_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_114_) {
        0 => {
            let mut v_it_118_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_119_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_117_);
            lean_dec(v_h__2_116_);
            v_it_118_ = lean_ctor_get(v_x_114_, 0);
            lean_inc(v_it_118_);
            v_out_119_ = lean_ctor_get(v_x_114_, 1);
            lean_inc(v_out_119_);
            lean_dec_ref_known(v_x_114_, 2);
            v___x_120_ = lean_apply_2(v_h__1_115_, v_it_118_, v_out_119_);
            return v___x_120_;
        }
        1 => {
            let mut v_it_121_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_117_);
            lean_dec(v_h__1_115_);
            v_it_121_ = lean_ctor_get(v_x_114_, 0);
            lean_inc(v_it_121_);
            lean_dec_ref_known(v_x_114_, 1);
            v___x_122_ = lean_apply_1(v_h__2_116_, v_it_121_);
            return v___x_122_;
        }
        _ => {
            let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_116_);
            lean_dec(v_h__1_115_);
            v___x_123_ = lean_box(0);
            v___x_124_ = lean_apply_1(v_h__3_117_, v___x_123_);
            return v___x_124_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
}

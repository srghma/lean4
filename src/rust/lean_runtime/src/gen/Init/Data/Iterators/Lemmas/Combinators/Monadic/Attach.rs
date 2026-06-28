// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.Attach
// Imports: Init.Data.Iterators.Combinators.Monadic.Attach Init.Data.Iterators.Combinators.Monadic.Attach Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.List.Attach Init.Data.Array.Lemmas Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop Init.Data.Iterators.Lemmas.Monadic.Basic
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::Attach::{
    initialize_Init_Data_Iterators_Combinators_Monadic_Attach,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Monadic::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
};
use crate::r#gen::Init::Data::List::Attach::{
    initialize_Init_Data_List_Attach, runtime_initialize_Init_Data_List_Attach,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_66_: *mut LeanObject,
    mut v_h__1_67_: *mut LeanObject,
    mut v_h__2_68_: *mut LeanObject,
    mut v_h__3_69_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_66_) {
        0 => {
            let mut v_it_70_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_71_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_69_);
            lean_dec(v_h__2_68_);
            v_it_70_ = lean_ctor_get(v_x_66_, 0);
            lean_inc(v_it_70_);
            v_out_71_ = lean_ctor_get(v_x_66_, 1);
            lean_inc(v_out_71_);
            lean_dec_ref_known(v_x_66_, 2);
            v___x_72_ = lean_apply_2(v_h__1_67_, v_it_70_, v_out_71_);
            return v___x_72_;
        }
        1 => {
            let mut v_it_73_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_69_);
            lean_dec(v_h__1_67_);
            v_it_73_ = lean_ctor_get(v_x_66_, 0);
            lean_inc(v_it_73_);
            lean_dec_ref_known(v_x_66_, 1);
            v___x_74_ = lean_apply_1(v_h__2_68_, v_it_73_);
            return v___x_74_;
        }
        _ => {
            let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_68_);
            lean_dec(v_h__1_67_);
            v___x_75_ = lean_box(0);
            v___x_76_ = lean_apply_1(v_h__3_69_, v___x_75_);
            return v___x_76_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_77_: *mut LeanObject,
    mut v_00_u03b2_78_: *mut LeanObject,
    mut v_m_79_: *mut LeanObject,
    mut v_motive_80_: *mut LeanObject,
    mut v_x_81_: *mut LeanObject,
    mut v_h__1_82_: *mut LeanObject,
    mut v_h__2_83_: *mut LeanObject,
    mut v_h__3_84_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_81_) {
        0 => {
            let mut v_it_85_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_86_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_84_);
            lean_dec(v_h__2_83_);
            v_it_85_ = lean_ctor_get(v_x_81_, 0);
            lean_inc(v_it_85_);
            v_out_86_ = lean_ctor_get(v_x_81_, 1);
            lean_inc(v_out_86_);
            lean_dec_ref_known(v_x_81_, 2);
            v___x_87_ = lean_apply_2(v_h__1_82_, v_it_85_, v_out_86_);
            return v___x_87_;
        }
        1 => {
            let mut v_it_88_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_84_);
            lean_dec(v_h__1_82_);
            v_it_88_ = lean_ctor_get(v_x_81_, 0);
            lean_inc(v_it_88_);
            lean_dec_ref_known(v_x_81_, 1);
            v___x_89_ = lean_apply_1(v_h__2_83_, v_it_88_);
            return v___x_89_;
        }
        _ => {
            let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_83_);
            lean_dec(v_h__1_82_);
            v___x_90_ = lean_box(0);
            v___x_91_ = lean_apply_1(v_h__3_84_, v___x_90_);
            return v___x_91_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___redArg(
    mut v_step_92_: *mut LeanObject,
    mut v_h__1_93_: *mut LeanObject,
    mut v_h__2_94_: *mut LeanObject,
    mut v_h__3_95_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_step_92_) {
        0 => {
            let mut v_it_96_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_97_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_95_);
            lean_dec(v_h__2_94_);
            v_it_96_ = lean_ctor_get(v_step_92_, 0);
            lean_inc(v_it_96_);
            v_out_97_ = lean_ctor_get(v_step_92_, 1);
            lean_inc(v_out_97_);
            lean_dec_ref_known(v_step_92_, 2);
            v___x_98_ = lean_apply_3(v_h__1_93_, v_it_96_, v_out_97_, lean_box(0));
            return v___x_98_;
        }
        1 => {
            let mut v_it_99_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_95_);
            lean_dec(v_h__1_93_);
            v_it_99_ = lean_ctor_get(v_step_92_, 0);
            lean_inc(v_it_99_);
            lean_dec_ref_known(v_step_92_, 1);
            v___x_100_ = lean_apply_2(v_h__2_94_, v_it_99_, lean_box(0));
            return v___x_100_;
        }
        _ => {
            let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_94_);
            lean_dec(v_h__1_93_);
            v___x_101_ = lean_apply_1(v_h__3_95_, lean_box(0));
            return v___x_101_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(
    mut v_00_u03b1_102_: *mut LeanObject,
    mut v_m_103_: *mut LeanObject,
    mut v_00_u03b2_104_: *mut LeanObject,
    mut v_inst_105_: *mut LeanObject,
    mut v_P_106_: *mut LeanObject,
    mut v_it_107_: *mut LeanObject,
    mut v_motive_108_: *mut LeanObject,
    mut v_step_109_: *mut LeanObject,
    mut v_h__1_110_: *mut LeanObject,
    mut v_h__2_111_: *mut LeanObject,
    mut v_h__3_112_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_step_109_) {
        0 => {
            let mut v_it_113_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_114_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_112_);
            lean_dec(v_h__2_111_);
            v_it_113_ = lean_ctor_get(v_step_109_, 0);
            lean_inc(v_it_113_);
            v_out_114_ = lean_ctor_get(v_step_109_, 1);
            lean_inc(v_out_114_);
            lean_dec_ref_known(v_step_109_, 2);
            v___x_115_ = lean_apply_3(v_h__1_110_, v_it_113_, v_out_114_, lean_box(0));
            return v___x_115_;
        }
        1 => {
            let mut v_it_116_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_112_);
            lean_dec(v_h__1_110_);
            v_it_116_ = lean_ctor_get(v_step_109_, 0);
            lean_inc(v_it_116_);
            lean_dec_ref_known(v_step_109_, 1);
            v___x_117_ = lean_apply_2(v_h__2_111_, v_it_116_, lean_box(0));
            return v___x_117_;
        }
        _ => {
            let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_111_);
            lean_dec(v_h__1_110_);
            v___x_118_ = lean_apply_1(v_h__3_112_, lean_box(0));
            return v___x_118_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___boxed(
    mut v_00_u03b1_119_: *mut LeanObject,
    mut v_m_120_: *mut LeanObject,
    mut v_00_u03b2_121_: *mut LeanObject,
    mut v_inst_122_: *mut LeanObject,
    mut v_P_123_: *mut LeanObject,
    mut v_it_124_: *mut LeanObject,
    mut v_motive_125_: *mut LeanObject,
    mut v_step_126_: *mut LeanObject,
    mut v_h__1_127_: *mut LeanObject,
    mut v_h__2_128_: *mut LeanObject,
    mut v_h__3_129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_130_: *mut LeanObject = core::ptr::null_mut();
    v_res_130_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(v_00_u03b1_119_, v_m_120_, v_00_u03b2_121_, v_inst_122_, v_P_123_, v_it_124_, v_motive_125_, v_step_126_, v_h__1_127_, v_h__2_128_, v_h__3_129_);
    lean_dec(v_it_124_);
    lean_dec(v_inst_122_);
    return v_res_130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(builtin);
}

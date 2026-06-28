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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_66_: *mut crate::leanh::LeanObject,
    mut v_h__1_67_: *mut crate::leanh::LeanObject,
    mut v_h__2_68_: *mut crate::leanh::LeanObject,
    mut v_h__3_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_66_) {
        0 => {
            let mut v_it_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_69_);
            crate::leanh::lean_dec(v_h__2_68_);
            v_it_70_ = crate::leanh::lean_ctor_get(v_x_66_, 0);
            crate::leanh::lean_inc(v_it_70_);
            v_out_71_ = crate::leanh::lean_ctor_get(v_x_66_, 1);
            crate::leanh::lean_inc(v_out_71_);
            crate::leanh::lean_dec_ref_known(v_x_66_, 2);
            v___x_72_ = crate::leanh::lean_apply_2(v_h__1_67_, v_it_70_, v_out_71_);
            return v___x_72_;
        }
        1 => {
            let mut v_it_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_69_);
            crate::leanh::lean_dec(v_h__1_67_);
            v_it_73_ = crate::leanh::lean_ctor_get(v_x_66_, 0);
            crate::leanh::lean_inc(v_it_73_);
            crate::leanh::lean_dec_ref_known(v_x_66_, 1);
            v___x_74_ = crate::leanh::lean_apply_1(v_h__2_68_, v_it_73_);
            return v___x_74_;
        }
        _ => {
            let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_68_);
            crate::leanh::lean_dec(v_h__1_67_);
            v___x_75_ = crate::leanh::lean_box(0);
            v___x_76_ = crate::leanh::lean_apply_1(v_h__3_69_, v___x_75_);
            return v___x_76_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_77_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_78_: *mut crate::leanh::LeanObject,
    mut v_m_79_: *mut crate::leanh::LeanObject,
    mut v_motive_80_: *mut crate::leanh::LeanObject,
    mut v_x_81_: *mut crate::leanh::LeanObject,
    mut v_h__1_82_: *mut crate::leanh::LeanObject,
    mut v_h__2_83_: *mut crate::leanh::LeanObject,
    mut v_h__3_84_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_81_) {
        0 => {
            let mut v_it_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_84_);
            crate::leanh::lean_dec(v_h__2_83_);
            v_it_85_ = crate::leanh::lean_ctor_get(v_x_81_, 0);
            crate::leanh::lean_inc(v_it_85_);
            v_out_86_ = crate::leanh::lean_ctor_get(v_x_81_, 1);
            crate::leanh::lean_inc(v_out_86_);
            crate::leanh::lean_dec_ref_known(v_x_81_, 2);
            v___x_87_ = crate::leanh::lean_apply_2(v_h__1_82_, v_it_85_, v_out_86_);
            return v___x_87_;
        }
        1 => {
            let mut v_it_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_84_);
            crate::leanh::lean_dec(v_h__1_82_);
            v_it_88_ = crate::leanh::lean_ctor_get(v_x_81_, 0);
            crate::leanh::lean_inc(v_it_88_);
            crate::leanh::lean_dec_ref_known(v_x_81_, 1);
            v___x_89_ = crate::leanh::lean_apply_1(v_h__2_83_, v_it_88_);
            return v___x_89_;
        }
        _ => {
            let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_83_);
            crate::leanh::lean_dec(v_h__1_82_);
            v___x_90_ = crate::leanh::lean_box(0);
            v___x_91_ = crate::leanh::lean_apply_1(v_h__3_84_, v___x_90_);
            return v___x_91_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___redArg(
    mut v_step_92_: *mut crate::leanh::LeanObject,
    mut v_h__1_93_: *mut crate::leanh::LeanObject,
    mut v_h__2_94_: *mut crate::leanh::LeanObject,
    mut v_h__3_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_step_92_) {
        0 => {
            let mut v_it_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_95_);
            crate::leanh::lean_dec(v_h__2_94_);
            v_it_96_ = crate::leanh::lean_ctor_get(v_step_92_, 0);
            crate::leanh::lean_inc(v_it_96_);
            v_out_97_ = crate::leanh::lean_ctor_get(v_step_92_, 1);
            crate::leanh::lean_inc(v_out_97_);
            crate::leanh::lean_dec_ref_known(v_step_92_, 2);
            v___x_98_ = crate::leanh::lean_apply_3(
                v_h__1_93_,
                v_it_96_,
                v_out_97_,
                crate::leanh::lean_box(0),
            );
            return v___x_98_;
        }
        1 => {
            let mut v_it_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_95_);
            crate::leanh::lean_dec(v_h__1_93_);
            v_it_99_ = crate::leanh::lean_ctor_get(v_step_92_, 0);
            crate::leanh::lean_inc(v_it_99_);
            crate::leanh::lean_dec_ref_known(v_step_92_, 1);
            v___x_100_ =
                crate::leanh::lean_apply_2(v_h__2_94_, v_it_99_, crate::leanh::lean_box(0));
            return v___x_100_;
        }
        _ => {
            let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_94_);
            crate::leanh::lean_dec(v_h__1_93_);
            v___x_101_ = crate::leanh::lean_apply_1(v_h__3_95_, crate::leanh::lean_box(0));
            return v___x_101_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(
    mut v_00_u03b1_102_: *mut crate::leanh::LeanObject,
    mut v_m_103_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_104_: *mut crate::leanh::LeanObject,
    mut v_inst_105_: *mut crate::leanh::LeanObject,
    mut v_P_106_: *mut crate::leanh::LeanObject,
    mut v_it_107_: *mut crate::leanh::LeanObject,
    mut v_motive_108_: *mut crate::leanh::LeanObject,
    mut v_step_109_: *mut crate::leanh::LeanObject,
    mut v_h__1_110_: *mut crate::leanh::LeanObject,
    mut v_h__2_111_: *mut crate::leanh::LeanObject,
    mut v_h__3_112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_step_109_) {
        0 => {
            let mut v_it_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_112_);
            crate::leanh::lean_dec(v_h__2_111_);
            v_it_113_ = crate::leanh::lean_ctor_get(v_step_109_, 0);
            crate::leanh::lean_inc(v_it_113_);
            v_out_114_ = crate::leanh::lean_ctor_get(v_step_109_, 1);
            crate::leanh::lean_inc(v_out_114_);
            crate::leanh::lean_dec_ref_known(v_step_109_, 2);
            v___x_115_ = crate::leanh::lean_apply_3(
                v_h__1_110_,
                v_it_113_,
                v_out_114_,
                crate::leanh::lean_box(0),
            );
            return v___x_115_;
        }
        1 => {
            let mut v_it_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_112_);
            crate::leanh::lean_dec(v_h__1_110_);
            v_it_116_ = crate::leanh::lean_ctor_get(v_step_109_, 0);
            crate::leanh::lean_inc(v_it_116_);
            crate::leanh::lean_dec_ref_known(v_step_109_, 1);
            v___x_117_ =
                crate::leanh::lean_apply_2(v_h__2_111_, v_it_116_, crate::leanh::lean_box(0));
            return v___x_117_;
        }
        _ => {
            let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_111_);
            crate::leanh::lean_dec(v_h__1_110_);
            v___x_118_ = crate::leanh::lean_apply_1(v_h__3_112_, crate::leanh::lean_box(0));
            return v___x_118_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___boxed(
    mut v_00_u03b1_119_: *mut crate::leanh::LeanObject,
    mut v_m_120_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_121_: *mut crate::leanh::LeanObject,
    mut v_inst_122_: *mut crate::leanh::LeanObject,
    mut v_P_123_: *mut crate::leanh::LeanObject,
    mut v_it_124_: *mut crate::leanh::LeanObject,
    mut v_motive_125_: *mut crate::leanh::LeanObject,
    mut v_step_126_: *mut crate::leanh::LeanObject,
    mut v_h__1_127_: *mut crate::leanh::LeanObject,
    mut v_h__2_128_: *mut crate::leanh::LeanObject,
    mut v_h__3_129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_130_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(v_00_u03b1_119_, v_m_120_, v_00_u03b2_121_, v_inst_122_, v_P_123_, v_it_124_, v_motive_125_, v_step_126_, v_h__1_127_, v_h__2_128_, v_h__3_129_);
    crate::leanh::lean_dec(v_it_124_);
    crate::leanh::lean_dec(v_inst_122_);
    return v_res_130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(builtin);
}

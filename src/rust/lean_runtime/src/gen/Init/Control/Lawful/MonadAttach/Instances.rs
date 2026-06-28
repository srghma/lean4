// Lean compiler output
// Module: Init.Control.Lawful.MonadAttach.Instances
// Imports: Init.Control.Lawful.MonadAttach.Lemmas Init.Control.Lawful.Basic Init.Control.State Init.Control.StateRef Init.Ext
use crate::r#gen::Init::Control::Lawful::Basic::{
    initialize_Init_Control_Lawful_Basic, runtime_initialize_Init_Control_Lawful_Basic,
};
use crate::r#gen::Init::Control::Lawful::MonadAttach::Lemmas::{
    initialize_Init_Control_Lawful_MonadAttach_Lemmas,
    runtime_initialize_Init_Control_Lawful_MonadAttach_Lemmas,
};
use crate::r#gen::Init::Control::State::{
    initialize_Init_Control_State, runtime_initialize_Init_Control_State,
};
use crate::r#gen::Init::Control::StateRef::{
    initialize_Init_Control_StateRef, runtime_initialize_Init_Control_StateRef,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___redArg(
    mut v_a_68_: *mut LeanObject,
    mut v_h__1_69_: *mut LeanObject,
    mut v_h__2_70_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_68_) == 0 {
        let mut v_a_71_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_69_);
        v_a_71_ = lean_ctor_get(v_a_68_, 0);
        lean_inc(v_a_71_);
        lean_dec_ref_known(v_a_68_, 1);
        v___x_72_ = lean_apply_2(v_h__2_70_, v_a_71_, lean_box(0));
        return v___x_72_;
    } else {
        let mut v_a_73_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_70_);
        v_a_73_ = lean_ctor_get(v_a_68_, 0);
        lean_inc(v_a_73_);
        lean_dec_ref_known(v_a_68_, 1);
        v___x_74_ = lean_apply_2(v_h__1_69_, v_a_73_, lean_box(0));
        return v___x_74_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter(
    mut v_m_75_: *mut LeanObject,
    mut v_00_u03b5_76_: *mut LeanObject,
    mut v_inst_77_: *mut LeanObject,
    mut v_00_u03b1_78_: *mut LeanObject,
    mut v_x_79_: *mut LeanObject,
    mut v_motive_80_: *mut LeanObject,
    mut v_a_81_: *mut LeanObject,
    mut v_h_82_: *mut LeanObject,
    mut v_h__1_83_: *mut LeanObject,
    mut v_h__2_84_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_81_) == 0 {
        let mut v_a_85_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_83_);
        v_a_85_ = lean_ctor_get(v_a_81_, 0);
        lean_inc(v_a_85_);
        lean_dec_ref_known(v_a_81_, 1);
        v___x_86_ = lean_apply_2(v_h__2_84_, v_a_85_, lean_box(0));
        return v___x_86_;
    } else {
        let mut v_a_87_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_84_);
        v_a_87_ = lean_ctor_get(v_a_81_, 0);
        lean_inc(v_a_87_);
        lean_dec_ref_known(v_a_81_, 1);
        v___x_88_ = lean_apply_2(v_h__1_83_, v_a_87_, lean_box(0));
        return v___x_88_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___boxed(
    mut v_m_89_: *mut LeanObject,
    mut v_00_u03b5_90_: *mut LeanObject,
    mut v_inst_91_: *mut LeanObject,
    mut v_00_u03b1_92_: *mut LeanObject,
    mut v_x_93_: *mut LeanObject,
    mut v_motive_94_: *mut LeanObject,
    mut v_a_95_: *mut LeanObject,
    mut v_h_96_: *mut LeanObject,
    mut v_h__1_97_: *mut LeanObject,
    mut v_h__2_98_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_99_: *mut LeanObject = core::ptr::null_mut();
    v_res_99_ = l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter(v_m_89_, v_00_u03b5_90_, v_inst_91_, v_00_u03b1_92_, v_x_93_, v_motive_94_, v_a_95_, v_h_96_, v_h__1_97_, v_h__2_98_);
    lean_dec(v_x_93_);
    lean_dec(v_inst_91_);
    return v_res_99_;
}
pub unsafe fn l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(
    mut v_x_100_: *mut LeanObject,
    mut v_h__1_101_: *mut LeanObject,
    mut v_h__2_102_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_100_) == 0 {
        let mut v_a_103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_101_);
        v_a_103_ = lean_ctor_get(v_x_100_, 0);
        lean_inc(v_a_103_);
        lean_dec_ref_known(v_x_100_, 1);
        v___x_104_ = lean_apply_1(v_h__2_102_, v_a_103_);
        return v___x_104_;
    } else {
        let mut v_a_105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_102_);
        v_a_105_ = lean_ctor_get(v_x_100_, 0);
        lean_inc(v_a_105_);
        lean_dec_ref_known(v_x_100_, 1);
        v___x_106_ = lean_apply_1(v_h__1_101_, v_a_105_);
        return v___x_106_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter(
    mut v_00_u03b5_107_: *mut LeanObject,
    mut v_00_u03b1_108_: *mut LeanObject,
    mut v_motive_109_: *mut LeanObject,
    mut v_x_110_: *mut LeanObject,
    mut v_h__1_111_: *mut LeanObject,
    mut v_h__2_112_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_110_) == 0 {
        let mut v_a_113_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_111_);
        v_a_113_ = lean_ctor_get(v_x_110_, 0);
        lean_inc(v_a_113_);
        lean_dec_ref_known(v_x_110_, 1);
        v___x_114_ = lean_apply_1(v_h__2_112_, v_a_113_);
        return v___x_114_;
    } else {
        let mut v_a_115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_112_);
        v_a_115_ = lean_ctor_get(v_x_110_, 0);
        lean_inc(v_a_115_);
        lean_dec_ref_known(v_x_110_, 1);
        v___x_116_ = lean_apply_1(v_h__1_111_, v_a_115_);
        return v___x_116_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter___redArg(
    mut v_a_117_: *mut LeanObject,
    mut v_h__1_118_: *mut LeanObject,
    mut v_h__2_119_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_117_) == 0 {
        let mut v_a_120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_118_);
        v_a_120_ = lean_ctor_get(v_a_117_, 0);
        lean_inc(v_a_120_);
        lean_dec_ref_known(v_a_117_, 1);
        v___x_121_ = lean_apply_1(v_h__2_119_, v_a_120_);
        return v___x_121_;
    } else {
        let mut v_a_122_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_119_);
        v_a_122_ = lean_ctor_get(v_a_117_, 0);
        lean_inc(v_a_122_);
        lean_dec_ref_known(v_a_117_, 1);
        v___x_123_ = lean_apply_1(v_h__1_118_, v_a_122_);
        return v___x_123_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter(
    mut v_00_u03b5_124_: *mut LeanObject,
    mut v_00_u03b1_125_: *mut LeanObject,
    mut v_P_126_: *mut LeanObject,
    mut v_motive_127_: *mut LeanObject,
    mut v_a_128_: *mut LeanObject,
    mut v_h__1_129_: *mut LeanObject,
    mut v_h__2_130_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_128_) == 0 {
        let mut v_a_131_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_129_);
        v_a_131_ = lean_ctor_get(v_a_128_, 0);
        lean_inc(v_a_131_);
        lean_dec_ref_known(v_a_128_, 1);
        v___x_132_ = lean_apply_1(v_h__2_130_, v_a_131_);
        return v___x_132_;
    } else {
        let mut v_a_133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_130_);
        v_a_133_ = lean_ctor_get(v_a_128_, 0);
        lean_inc(v_a_133_);
        lean_dec_ref_known(v_a_128_, 1);
        v___x_134_ = lean_apply_1(v_h__1_129_, v_a_133_);
        return v___x_134_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Lawful_MonadAttach_Instances(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful_MonadAttach_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateRef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Lawful_MonadAttach_Instances(
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
pub unsafe fn initialize_Init_Control_Lawful_MonadAttach_Instances(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful_MonadAttach_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Lawful_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_State(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_StateRef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_MonadAttach_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_Lawful_MonadAttach_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_Lawful_MonadAttach_Instances(builtin);
}

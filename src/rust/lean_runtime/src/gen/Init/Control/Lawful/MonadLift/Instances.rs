// Lean compiler output
// Module: Init.Control.Lawful.MonadLift.Instances
// Imports: Init.Control.Option Init.Control.Except Init.Control.ExceptCps Init.Control.ExceptCps Init.Control.StateRef Init.Control.StateCps Init.Control.StateCps Init.Control.Id Init.Control.Lawful.MonadLift.Basic Init.Control.Option Init.Control.State Init.Control.StateRef Init.Control.Lawful.Instances Init.Control.Lawful.MonadLift.Lemmas
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::Control::ExceptCps::{
    initialize_Init_Control_ExceptCps, runtime_initialize_Init_Control_ExceptCps,
};
use crate::r#gen::Init::Control::Id::{
    initialize_Init_Control_Id, runtime_initialize_Init_Control_Id,
};
use crate::r#gen::Init::Control::Lawful::Instances::{
    initialize_Init_Control_Lawful_Instances, runtime_initialize_Init_Control_Lawful_Instances,
};
use crate::r#gen::Init::Control::Lawful::MonadLift::Basic::{
    initialize_Init_Control_Lawful_MonadLift_Basic,
    runtime_initialize_Init_Control_Lawful_MonadLift_Basic,
};
use crate::r#gen::Init::Control::Lawful::MonadLift::Lemmas::{
    initialize_Init_Control_Lawful_MonadLift_Lemmas,
    runtime_initialize_Init_Control_Lawful_MonadLift_Lemmas,
};
use crate::r#gen::Init::Control::Option::{
    initialize_Init_Control_Option, runtime_initialize_Init_Control_Option,
};
use crate::r#gen::Init::Control::State::{
    initialize_Init_Control_State, runtime_initialize_Init_Control_State,
};
use crate::r#gen::Init::Control::StateCps::{
    initialize_Init_Control_StateCps, runtime_initialize_Init_Control_StateCps,
};
use crate::r#gen::Init::Control::StateRef::{
    initialize_Init_Control_StateRef, runtime_initialize_Init_Control_StateRef,
};
pub unsafe fn l___private_Init_Control_Lawful_MonadLift_Instances_0__OptionT_bind_match__1_splitter___redArg(
    mut v_____do__lift_51_: *mut crate::leanh::LeanObject,
    mut v_h__1_52_: *mut crate::leanh::LeanObject,
    mut v_h__2_53_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_51_) == 0 {
        let mut v___x_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_52_);
        v___x_54_ = crate::leanh::lean_box(0);
        v___x_55_ = crate::leanh::lean_apply_1(v_h__2_53_, v___x_54_);
        return v___x_55_;
    } else {
        let mut v_val_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_53_);
        v_val_56_ = crate::leanh::lean_ctor_get(v_____do__lift_51_, 0);
        crate::leanh::lean_inc(v_val_56_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_51_, 1);
        v___x_57_ = crate::leanh::lean_apply_1(v_h__1_52_, v_val_56_);
        return v___x_57_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_MonadLift_Instances_0__OptionT_bind_match__1_splitter(
    mut v_00_u03b1_58_: *mut crate::leanh::LeanObject,
    mut v_motive_59_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_60_: *mut crate::leanh::LeanObject,
    mut v_h__1_61_: *mut crate::leanh::LeanObject,
    mut v_h__2_62_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_60_) == 0 {
        let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_61_);
        v___x_63_ = crate::leanh::lean_box(0);
        v___x_64_ = crate::leanh::lean_apply_1(v_h__2_62_, v___x_63_);
        return v___x_64_;
    } else {
        let mut v_val_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_62_);
        v_val_65_ = crate::leanh::lean_ctor_get(v_____do__lift_60_, 0);
        crate::leanh::lean_inc(v_val_65_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_60_, 1);
        v___x_66_ = crate::leanh::lean_apply_1(v_h__1_61_, v_val_65_);
        return v___x_66_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_MonadLift_Instances_0__Except_map_match__1_splitter___redArg(
    mut v_x_67_: *mut crate::leanh::LeanObject,
    mut v_h__1_68_: *mut crate::leanh::LeanObject,
    mut v_h__2_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_67_) == 0 {
        let mut v_a_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_69_);
        v_a_70_ = crate::leanh::lean_ctor_get(v_x_67_, 0);
        crate::leanh::lean_inc(v_a_70_);
        crate::leanh::lean_dec_ref_known(v_x_67_, 1);
        v___x_71_ = crate::leanh::lean_apply_1(v_h__1_68_, v_a_70_);
        return v___x_71_;
    } else {
        let mut v_a_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_68_);
        v_a_72_ = crate::leanh::lean_ctor_get(v_x_67_, 0);
        crate::leanh::lean_inc(v_a_72_);
        crate::leanh::lean_dec_ref_known(v_x_67_, 1);
        v___x_73_ = crate::leanh::lean_apply_1(v_h__2_69_, v_a_72_);
        return v___x_73_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_MonadLift_Instances_0__Except_map_match__1_splitter(
    mut v_00_u03b5_74_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_75_: *mut crate::leanh::LeanObject,
    mut v_motive_76_: *mut crate::leanh::LeanObject,
    mut v_x_77_: *mut crate::leanh::LeanObject,
    mut v_h__1_78_: *mut crate::leanh::LeanObject,
    mut v_h__2_79_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_77_) == 0 {
        let mut v_a_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_79_);
        v_a_80_ = crate::leanh::lean_ctor_get(v_x_77_, 0);
        crate::leanh::lean_inc(v_a_80_);
        crate::leanh::lean_dec_ref_known(v_x_77_, 1);
        v___x_81_ = crate::leanh::lean_apply_1(v_h__1_78_, v_a_80_);
        return v___x_81_;
    } else {
        let mut v_a_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_78_);
        v_a_82_ = crate::leanh::lean_ctor_get(v_x_77_, 0);
        crate::leanh::lean_inc(v_a_82_);
        crate::leanh::lean_dec_ref_known(v_x_77_, 1);
        v___x_83_ = crate::leanh::lean_apply_1(v_h__2_79_, v_a_82_);
        return v___x_83_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_MonadLift_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(
    mut v_x_84_: *mut crate::leanh::LeanObject,
    mut v_h__1_85_: *mut crate::leanh::LeanObject,
    mut v_h__2_86_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_84_) == 0 {
        let mut v_a_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_85_);
        v_a_87_ = crate::leanh::lean_ctor_get(v_x_84_, 0);
        crate::leanh::lean_inc(v_a_87_);
        crate::leanh::lean_dec_ref_known(v_x_84_, 1);
        v___x_88_ = crate::leanh::lean_apply_1(v_h__2_86_, v_a_87_);
        return v___x_88_;
    } else {
        let mut v_a_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_86_);
        v_a_89_ = crate::leanh::lean_ctor_get(v_x_84_, 0);
        crate::leanh::lean_inc(v_a_89_);
        crate::leanh::lean_dec_ref_known(v_x_84_, 1);
        v___x_90_ = crate::leanh::lean_apply_1(v_h__1_85_, v_a_89_);
        return v___x_90_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_MonadLift_Instances_0__ExceptT_bindCont_match__1_splitter(
    mut v_00_u03b5_91_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_92_: *mut crate::leanh::LeanObject,
    mut v_motive_93_: *mut crate::leanh::LeanObject,
    mut v_x_94_: *mut crate::leanh::LeanObject,
    mut v_h__1_95_: *mut crate::leanh::LeanObject,
    mut v_h__2_96_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_94_) == 0 {
        let mut v_a_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_95_);
        v_a_97_ = crate::leanh::lean_ctor_get(v_x_94_, 0);
        crate::leanh::lean_inc(v_a_97_);
        crate::leanh::lean_dec_ref_known(v_x_94_, 1);
        v___x_98_ = crate::leanh::lean_apply_1(v_h__2_96_, v_a_97_);
        return v___x_98_;
    } else {
        let mut v_a_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_96_);
        v_a_99_ = crate::leanh::lean_ctor_get(v_x_94_, 0);
        crate::leanh::lean_inc(v_a_99_);
        crate::leanh::lean_dec_ref_known(v_x_94_, 1);
        v___x_100_ = crate::leanh::lean_apply_1(v_h__1_95_, v_a_99_);
        return v___x_100_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Lawful_MonadLift_Instances(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_ExceptCps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_ExceptCps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateRef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateCps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateCps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_MonadLift_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateRef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_MonadLift_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Lawful_MonadLift_Instances(
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
pub unsafe fn initialize_Init_Control_Lawful_MonadLift_Instances(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_ExceptCps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_ExceptCps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_StateRef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_StateCps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_StateCps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Lawful_MonadLift_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_StateRef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Lawful_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Lawful_MonadLift_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_MonadLift_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Lawful_MonadLift_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_Lawful_MonadLift_Instances(builtin);
}

// Lean compiler output
// Module: Lake.Util.Exit
// Imports: Init.Notation Init.Data.UInt.BasicAux
use crate::ffi::lean_uint32_dec_eq;
use crate::r#gen::Init::Data::UInt::BasicAux::{
    initialize_Init_Data_UInt_BasicAux, runtime_initialize_Init_Data_UInt_BasicAux,
};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
pub unsafe fn l_Lake_instMonadExitOfMonadLift___redArg___lam__0(
    mut v_inst_52_: *mut leanh::LeanObject,
    mut v_inst_53_: *mut leanh::LeanObject,
    mut v_00_u03b1_54_: *mut leanh::LeanObject,
    mut v_rc_55_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_56_ = leanh::lean_box_uint32(v_rc_55_);
    v___x_57_ = leanh::lean_apply_2(v_inst_52_, leanh::lean_box(0), v___x_56_);
    v___x_58_ = leanh::lean_apply_2(v_inst_53_, leanh::lean_box(0), v___x_57_);
    return v___x_58_;
}
pub unsafe fn l_Lake_instMonadExitOfMonadLift___redArg___lam__0___boxed(
    mut v_inst_59_: *mut leanh::LeanObject,
    mut v_inst_60_: *mut leanh::LeanObject,
    mut v_00_u03b1_61_: *mut leanh::LeanObject,
    mut v_rc_62_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rc_boxed_63_: u32 = 0;
    let mut v_res_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_rc_boxed_63_ = leanh::lean_unbox_uint32(v_rc_62_);
    leanh::lean_dec(v_rc_62_);
    v_res_64_ = l_Lake_instMonadExitOfMonadLift___redArg___lam__0(
        v_inst_59_,
        v_inst_60_,
        v_00_u03b1_61_,
        v_rc_boxed_63_,
    );
    return v_res_64_;
}
pub unsafe fn l_Lake_instMonadExitOfMonadLift___redArg(
    mut v_inst_65_: *mut leanh::LeanObject,
    mut v_inst_66_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_67_ = leanh::lean_alloc_closure(
        l_Lake_instMonadExitOfMonadLift___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_67_, 0, v_inst_66_);
    leanh::lean_closure_set(v___f_67_, 1, v_inst_65_);
    return v___f_67_;
}
pub unsafe fn l_Lake_instMonadExitOfMonadLift(
    mut v_m_68_: *mut leanh::LeanObject,
    mut v_n_69_: *mut leanh::LeanObject,
    mut v_inst_70_: *mut leanh::LeanObject,
    mut v_inst_71_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_72_ = leanh::lean_alloc_closure(
        l_Lake_instMonadExitOfMonadLift___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_72_, 0, v_inst_71_);
    leanh::lean_closure_set(v___f_72_, 1, v_inst_70_);
    return v___f_72_;
}
pub unsafe fn l_Lake_exitIfErrorCode___redArg(
    mut v_inst_73_: *mut leanh::LeanObject,
    mut v_inst_74_: *mut leanh::LeanObject,
    mut v_rc_75_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_76_: u32 = 0;
    let mut v___x_77_: u8 = 0;
    v___x_76_ = 0;
    v___x_77_ = lean_uint32_dec_eq(v_rc_75_, v___x_76_);
    if v___x_77_ == 0 {
        let mut v___x_78_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_73_);
        v___x_78_ = leanh::lean_box_uint32(v_rc_75_);
        v___x_79_ = leanh::lean_apply_2(v_inst_74_, leanh::lean_box(0), v___x_78_);
        return v___x_79_;
    } else {
        let mut v___x_80_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_81_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_74_);
        v___x_80_ = leanh::lean_box(0);
        v___x_81_ = leanh::lean_apply_2(v_inst_73_, leanh::lean_box(0), v___x_80_);
        return v___x_81_;
    }
}
pub unsafe fn l_Lake_exitIfErrorCode___redArg___boxed(
    mut v_inst_82_: *mut leanh::LeanObject,
    mut v_inst_83_: *mut leanh::LeanObject,
    mut v_rc_84_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rc_boxed_85_: u32 = 0;
    let mut v_res_86_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_rc_boxed_85_ = leanh::lean_unbox_uint32(v_rc_84_);
    leanh::lean_dec(v_rc_84_);
    v_res_86_ = l_Lake_exitIfErrorCode___redArg(v_inst_82_, v_inst_83_, v_rc_boxed_85_);
    return v_res_86_;
}
pub unsafe fn l_Lake_exitIfErrorCode(
    mut v_m_87_: *mut leanh::LeanObject,
    mut v_inst_88_: *mut leanh::LeanObject,
    mut v_inst_89_: *mut leanh::LeanObject,
    mut v_rc_90_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_91_: u32 = 0;
    let mut v___x_92_: u8 = 0;
    v___x_91_ = 0;
    v___x_92_ = lean_uint32_dec_eq(v_rc_90_, v___x_91_);
    if v___x_92_ == 0 {
        let mut v___x_93_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_94_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_88_);
        v___x_93_ = leanh::lean_box_uint32(v_rc_90_);
        v___x_94_ = leanh::lean_apply_2(v_inst_89_, leanh::lean_box(0), v___x_93_);
        return v___x_94_;
    } else {
        let mut v___x_95_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_89_);
        v___x_95_ = leanh::lean_box(0);
        v___x_96_ = leanh::lean_apply_2(v_inst_88_, leanh::lean_box(0), v___x_95_);
        return v___x_96_;
    }
}
pub unsafe fn l_Lake_exitIfErrorCode___boxed(
    mut v_m_97_: *mut leanh::LeanObject,
    mut v_inst_98_: *mut leanh::LeanObject,
    mut v_inst_99_: *mut leanh::LeanObject,
    mut v_rc_100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rc_boxed_101_: u32 = 0;
    let mut v_res_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_rc_boxed_101_ = leanh::lean_unbox_uint32(v_rc_100_);
    leanh::lean_dec(v_rc_100_);
    v_res_102_ = l_Lake_exitIfErrorCode(v_m_97_, v_inst_98_, v_inst_99_, v_rc_boxed_101_);
    return v_res_102_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Exit(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Exit(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Exit(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Exit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Exit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Exit(builtin);
}
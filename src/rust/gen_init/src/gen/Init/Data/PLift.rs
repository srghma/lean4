// Lean compiler output
// Module: Init.Data.PLift
// Imports: Init.Core
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
pub unsafe fn l_instDecidableEqPLift_decEq___redArg(
    mut v_inst_45_: *mut leanh::LeanObject,
    mut v_x_46_: *mut leanh::LeanObject,
    mut v_x_47_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_48_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_49_: u8 = 0;
    v___x_48_ = leanh::lean_apply_2(v_inst_45_, v_x_46_, v_x_47_);
    v___x_49_ = (leanh::lean_unbox(v___x_48_) as u8);
    return v___x_49_;
}
pub unsafe fn l_instDecidableEqPLift_decEq___redArg___boxed(
    mut v_inst_50_: *mut leanh::LeanObject,
    mut v_x_51_: *mut leanh::LeanObject,
    mut v_x_52_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_53_: u8 = 0;
    let mut v_r_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_53_ = l_instDecidableEqPLift_decEq___redArg(v_inst_50_, v_x_51_, v_x_52_);
    v_r_54_ = leanh::lean_box((v_res_53_) as usize);
    return v_r_54_;
}
pub unsafe fn l_instDecidableEqPLift_decEq(
    mut v_00_u03b1_55_: *mut leanh::LeanObject,
    mut v_inst_56_: *mut leanh::LeanObject,
    mut v_x_57_: *mut leanh::LeanObject,
    mut v_x_58_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_60_: u8 = 0;
    v___x_59_ = leanh::lean_apply_2(v_inst_56_, v_x_57_, v_x_58_);
    v___x_60_ = (leanh::lean_unbox(v___x_59_) as u8);
    return v___x_60_;
}
pub unsafe fn l_instDecidableEqPLift_decEq___boxed(
    mut v_00_u03b1_61_: *mut leanh::LeanObject,
    mut v_inst_62_: *mut leanh::LeanObject,
    mut v_x_63_: *mut leanh::LeanObject,
    mut v_x_64_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_65_: u8 = 0;
    let mut v_r_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_65_ = l_instDecidableEqPLift_decEq(v_00_u03b1_61_, v_inst_62_, v_x_63_, v_x_64_);
    v_r_66_ = leanh::lean_box((v_res_65_) as usize);
    return v_r_66_;
}
pub unsafe fn l_instDecidableEqPLift___redArg(
    mut v_inst_67_: *mut leanh::LeanObject,
    mut v_x_68_: *mut leanh::LeanObject,
    mut v_x_69_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_71_: u8 = 0;
    v___x_70_ = leanh::lean_apply_2(v_inst_67_, v_x_68_, v_x_69_);
    v___x_71_ = (leanh::lean_unbox(v___x_70_) as u8);
    return v___x_71_;
}
pub unsafe fn l_instDecidableEqPLift___redArg___boxed(
    mut v_inst_72_: *mut leanh::LeanObject,
    mut v_x_73_: *mut leanh::LeanObject,
    mut v_x_74_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_75_: u8 = 0;
    let mut v_r_76_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_75_ = l_instDecidableEqPLift___redArg(v_inst_72_, v_x_73_, v_x_74_);
    v_r_76_ = leanh::lean_box((v_res_75_) as usize);
    return v_r_76_;
}
pub unsafe fn l_instDecidableEqPLift(
    mut v_00_u03b1_77_: *mut leanh::LeanObject,
    mut v_inst_78_: *mut leanh::LeanObject,
    mut v_x_79_: *mut leanh::LeanObject,
    mut v_x_80_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_81_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_82_: u8 = 0;
    v___x_81_ = leanh::lean_apply_2(v_inst_78_, v_x_79_, v_x_80_);
    v___x_82_ = (leanh::lean_unbox(v___x_81_) as u8);
    return v___x_82_;
}
pub unsafe fn l_instDecidableEqPLift___boxed(
    mut v_00_u03b1_83_: *mut leanh::LeanObject,
    mut v_inst_84_: *mut leanh::LeanObject,
    mut v_x_85_: *mut leanh::LeanObject,
    mut v_x_86_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_87_: u8 = 0;
    let mut v_r_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_87_ = l_instDecidableEqPLift(v_00_u03b1_83_, v_inst_84_, v_x_85_, v_x_86_);
    v_r_88_ = leanh::lean_box((v_res_87_) as usize);
    return v_r_88_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_PLift(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_PLift(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_PLift(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_PLift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_PLift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_PLift(builtin);
}
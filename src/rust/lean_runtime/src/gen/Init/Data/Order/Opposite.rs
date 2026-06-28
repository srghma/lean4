// Lean compiler output
// Module: Init.Data.Order.Opposite
// Imports: Init.Data.Order.ClassesExtra Init.Data.Order.Classes Init.Data.Order.FactoriesExtra Init.Data.Order.Lemmas
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Data::Order::ClassesExtra::{
    initialize_Init_Data_Order_ClassesExtra, runtime_initialize_Init_Data_Order_ClassesExtra,
};
use crate::r#gen::Init::Data::Order::FactoriesExtra::{
    initialize_Init_Data_Order_FactoriesExtra, runtime_initialize_Init_Data_Order_FactoriesExtra,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
pub unsafe fn l_LE_opposite(
    mut v_00_u03b1_77_: *mut crate::leanh::LeanObject,
    mut v_le_78_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_79_ = crate::leanh::lean_box(0);
    return v___x_79_;
}
pub unsafe fn l_LT_opposite(
    mut v_00_u03b1_80_: *mut crate::leanh::LeanObject,
    mut v_lt_81_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_82_ = crate::leanh::lean_box(0);
    return v___x_82_;
}
pub unsafe fn l_Min_oppositeMax___redArg___lam__0(
    mut v_min_83_: *mut crate::leanh::LeanObject,
    mut v_a_84_: *mut crate::leanh::LeanObject,
    mut v_b_85_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_86_ = crate::leanh::lean_apply_2(v_min_83_, v_a_84_, v_b_85_);
    return v___x_86_;
}
pub unsafe fn l_Min_oppositeMax___redArg(
    mut v_min_87_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_88_ = crate::leanh::lean_alloc_closure(
        l_Min_oppositeMax___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_88_, 0, v_min_87_);
    return v___f_88_;
}
pub unsafe fn l_Min_oppositeMax(
    mut v_00_u03b1_89_: *mut crate::leanh::LeanObject,
    mut v_min_90_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_91_ = crate::leanh::lean_alloc_closure(
        l_Min_oppositeMax___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_91_, 0, v_min_90_);
    return v___f_91_;
}
pub unsafe fn l_Max_oppositeMin___redArg___lam__0(
    mut v_max_92_: *mut crate::leanh::LeanObject,
    mut v_a_93_: *mut crate::leanh::LeanObject,
    mut v_b_94_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_95_ = crate::leanh::lean_apply_2(v_max_92_, v_a_93_, v_b_94_);
    return v___x_95_;
}
pub unsafe fn l_Max_oppositeMin___redArg(
    mut v_max_96_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_97_ = crate::leanh::lean_alloc_closure(
        l_Max_oppositeMin___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_97_, 0, v_max_96_);
    return v___f_97_;
}
pub unsafe fn l_Max_oppositeMin(
    mut v_00_u03b1_98_: *mut crate::leanh::LeanObject,
    mut v_max_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_100_ = crate::leanh::lean_alloc_closure(
        l_Max_oppositeMin___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_100_, 0, v_max_99_);
    return v___f_100_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(
    mut v_id_101_: *mut crate::leanh::LeanObject,
    mut v_a_102_: *mut crate::leanh::LeanObject,
    mut v_b_103_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_105_: u8 = 0;
    v___x_104_ = crate::leanh::lean_apply_2(v_id_101_, v_b_103_, v_a_102_);
    v___x_105_ = (crate::leanh::lean_unbox(v___x_104_) as u8);
    return v___x_105_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg___boxed(
    mut v_id_106_: *mut crate::leanh::LeanObject,
    mut v_a_107_: *mut crate::leanh::LeanObject,
    mut v_b_108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_109_: u8 = 0;
    let mut v_r_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_109_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(
        v_id_106_, v_a_107_, v_b_108_,
    );
    v_r_110_ = crate::leanh::lean_box((v_res_109_) as usize);
    return v_r_110_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLEOpposite(
    mut v_00_u03b1_111_: *mut crate::leanh::LeanObject,
    mut v_i_112_: *mut crate::leanh::LeanObject,
    mut v_id_113_: *mut crate::leanh::LeanObject,
    mut v_a_114_: *mut crate::leanh::LeanObject,
    mut v_b_115_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: u8 = 0;
    v___x_116_ = crate::leanh::lean_apply_2(v_id_113_, v_b_115_, v_a_114_);
    v___x_117_ = (crate::leanh::lean_unbox(v___x_116_) as u8);
    return v___x_117_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLEOpposite___boxed(
    mut v_00_u03b1_118_: *mut crate::leanh::LeanObject,
    mut v_i_119_: *mut crate::leanh::LeanObject,
    mut v_id_120_: *mut crate::leanh::LeanObject,
    mut v_a_121_: *mut crate::leanh::LeanObject,
    mut v_b_122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_123_: u8 = 0;
    let mut v_r_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_123_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite(
        v_00_u03b1_118_,
        v_i_119_,
        v_id_120_,
        v_a_121_,
        v_b_122_,
    );
    v_r_124_ = crate::leanh::lean_box((v_res_123_) as usize);
    return v_r_124_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(
    mut v_id_125_: *mut crate::leanh::LeanObject,
    mut v_a_126_: *mut crate::leanh::LeanObject,
    mut v_b_127_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: u8 = 0;
    v___x_128_ = crate::leanh::lean_apply_2(v_id_125_, v_b_127_, v_a_126_);
    v___x_129_ = (crate::leanh::lean_unbox(v___x_128_) as u8);
    return v___x_129_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg___boxed(
    mut v_id_130_: *mut crate::leanh::LeanObject,
    mut v_a_131_: *mut crate::leanh::LeanObject,
    mut v_b_132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_133_: u8 = 0;
    let mut v_r_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_133_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(
        v_id_130_, v_a_131_, v_b_132_,
    );
    v_r_134_ = crate::leanh::lean_box((v_res_133_) as usize);
    return v_r_134_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLTOpposite(
    mut v_00_u03b1_135_: *mut crate::leanh::LeanObject,
    mut v_i_136_: *mut crate::leanh::LeanObject,
    mut v_id_137_: *mut crate::leanh::LeanObject,
    mut v_a_138_: *mut crate::leanh::LeanObject,
    mut v_b_139_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: u8 = 0;
    v___x_140_ = crate::leanh::lean_apply_2(v_id_137_, v_b_139_, v_a_138_);
    v___x_141_ = (crate::leanh::lean_unbox(v___x_140_) as u8);
    return v___x_141_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLTOpposite___boxed(
    mut v_00_u03b1_142_: *mut crate::leanh::LeanObject,
    mut v_i_143_: *mut crate::leanh::LeanObject,
    mut v_id_144_: *mut crate::leanh::LeanObject,
    mut v_a_145_: *mut crate::leanh::LeanObject,
    mut v_b_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_147_: u8 = 0;
    let mut v_r_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_147_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite(
        v_00_u03b1_142_,
        v_i_143_,
        v_id_144_,
        v_a_145_,
        v_b_146_,
    );
    v_r_148_ = crate::leanh::lean_box((v_res_147_) as usize);
    return v_r_148_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instLETransOpposite(
    mut v_00_u03b1_149_: *mut crate::leanh::LeanObject,
    mut v_i_150_: *mut crate::leanh::LeanObject,
    mut v_inst_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = crate::leanh::lean_box(0);
    return v___x_152_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Order_Opposite(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_ClassesExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_FactoriesExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Order_Opposite(
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
pub unsafe fn initialize_Init_Data_Order_Opposite(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_ClassesExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_FactoriesExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Opposite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Order_Opposite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Order_Opposite(builtin);
}

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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_box, lean_closure_set,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox,
};
pub unsafe fn l_LE_opposite(
    mut v_00_u03b1_77_: *mut LeanObject,
    mut v_le_78_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
    v___x_79_ = lean_box(0);
    return v___x_79_;
}
pub unsafe fn l_LT_opposite(
    mut v_00_u03b1_80_: *mut LeanObject,
    mut v_lt_81_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
    v___x_82_ = lean_box(0);
    return v___x_82_;
}
pub unsafe fn l_Min_oppositeMax___redArg___lam__0(
    mut v_min_83_: *mut LeanObject,
    mut v_a_84_: *mut LeanObject,
    mut v_b_85_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
    v___x_86_ = lean_apply_2(v_min_83_, v_a_84_, v_b_85_);
    return v___x_86_;
}
pub unsafe fn l_Min_oppositeMax___redArg(mut v_min_87_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_88_: *mut LeanObject = core::ptr::null_mut();
    v___f_88_ = lean_alloc_closure(
        l_Min_oppositeMax___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_88_, 0, v_min_87_);
    return v___f_88_;
}
pub unsafe fn l_Min_oppositeMax(
    mut v_00_u03b1_89_: *mut LeanObject,
    mut v_min_90_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_91_: *mut LeanObject = core::ptr::null_mut();
    v___f_91_ = lean_alloc_closure(
        l_Min_oppositeMax___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_91_, 0, v_min_90_);
    return v___f_91_;
}
pub unsafe fn l_Max_oppositeMin___redArg___lam__0(
    mut v_max_92_: *mut LeanObject,
    mut v_a_93_: *mut LeanObject,
    mut v_b_94_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
    v___x_95_ = lean_apply_2(v_max_92_, v_a_93_, v_b_94_);
    return v___x_95_;
}
pub unsafe fn l_Max_oppositeMin___redArg(mut v_max_96_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_97_: *mut LeanObject = core::ptr::null_mut();
    v___f_97_ = lean_alloc_closure(
        l_Max_oppositeMin___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_97_, 0, v_max_96_);
    return v___f_97_;
}
pub unsafe fn l_Max_oppositeMin(
    mut v_00_u03b1_98_: *mut LeanObject,
    mut v_max_99_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_100_: *mut LeanObject = core::ptr::null_mut();
    v___f_100_ = lean_alloc_closure(
        l_Max_oppositeMin___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_100_, 0, v_max_99_);
    return v___f_100_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(
    mut v_id_101_: *mut LeanObject,
    mut v_a_102_: *mut LeanObject,
    mut v_b_103_: *mut LeanObject,
) -> u8 {
    let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_105_: u8 = 0;
    v___x_104_ = lean_apply_2(v_id_101_, v_b_103_, v_a_102_);
    v___x_105_ = (lean_unbox(v___x_104_) as u8);
    return v___x_105_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg___boxed(
    mut v_id_106_: *mut LeanObject,
    mut v_a_107_: *mut LeanObject,
    mut v_b_108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_109_: u8 = 0;
    let mut v_r_110_: *mut LeanObject = core::ptr::null_mut();
    v_res_109_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(
        v_id_106_, v_a_107_, v_b_108_,
    );
    v_r_110_ = lean_box((v_res_109_) as usize);
    return v_r_110_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLEOpposite(
    mut v_00_u03b1_111_: *mut LeanObject,
    mut v_i_112_: *mut LeanObject,
    mut v_id_113_: *mut LeanObject,
    mut v_a_114_: *mut LeanObject,
    mut v_b_115_: *mut LeanObject,
) -> u8 {
    let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_117_: u8 = 0;
    v___x_116_ = lean_apply_2(v_id_113_, v_b_115_, v_a_114_);
    v___x_117_ = (lean_unbox(v___x_116_) as u8);
    return v___x_117_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLEOpposite___boxed(
    mut v_00_u03b1_118_: *mut LeanObject,
    mut v_i_119_: *mut LeanObject,
    mut v_id_120_: *mut LeanObject,
    mut v_a_121_: *mut LeanObject,
    mut v_b_122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_123_: u8 = 0;
    let mut v_r_124_: *mut LeanObject = core::ptr::null_mut();
    v_res_123_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite(
        v_00_u03b1_118_,
        v_i_119_,
        v_id_120_,
        v_a_121_,
        v_b_122_,
    );
    v_r_124_ = lean_box((v_res_123_) as usize);
    return v_r_124_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(
    mut v_id_125_: *mut LeanObject,
    mut v_a_126_: *mut LeanObject,
    mut v_b_127_: *mut LeanObject,
) -> u8 {
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: u8 = 0;
    v___x_128_ = lean_apply_2(v_id_125_, v_b_127_, v_a_126_);
    v___x_129_ = (lean_unbox(v___x_128_) as u8);
    return v___x_129_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg___boxed(
    mut v_id_130_: *mut LeanObject,
    mut v_a_131_: *mut LeanObject,
    mut v_b_132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_133_: u8 = 0;
    let mut v_r_134_: *mut LeanObject = core::ptr::null_mut();
    v_res_133_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(
        v_id_130_, v_a_131_, v_b_132_,
    );
    v_r_134_ = lean_box((v_res_133_) as usize);
    return v_r_134_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLTOpposite(
    mut v_00_u03b1_135_: *mut LeanObject,
    mut v_i_136_: *mut LeanObject,
    mut v_id_137_: *mut LeanObject,
    mut v_a_138_: *mut LeanObject,
    mut v_b_139_: *mut LeanObject,
) -> u8 {
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_141_: u8 = 0;
    v___x_140_ = lean_apply_2(v_id_137_, v_b_139_, v_a_138_);
    v___x_141_ = (lean_unbox(v___x_140_) as u8);
    return v___x_141_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instDecidableLTOpposite___boxed(
    mut v_00_u03b1_142_: *mut LeanObject,
    mut v_i_143_: *mut LeanObject,
    mut v_id_144_: *mut LeanObject,
    mut v_a_145_: *mut LeanObject,
    mut v_b_146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_147_: u8 = 0;
    let mut v_r_148_: *mut LeanObject = core::ptr::null_mut();
    v_res_147_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite(
        v_00_u03b1_142_,
        v_i_143_,
        v_id_144_,
        v_a_145_,
        v_b_146_,
    );
    v_r_148_ = lean_box((v_res_147_) as usize);
    return v_r_148_;
}
pub unsafe fn l_Std_OppositeOrderInstances_instLETransOpposite(
    mut v_00_u03b1_149_: *mut LeanObject,
    mut v_i_150_: *mut LeanObject,
    mut v_inst_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
    v___x_152_ = lean_box(0);
    return v___x_152_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Order_Opposite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_ClassesExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_FactoriesExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Order_Opposite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Order_Opposite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_ClassesExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_FactoriesExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Opposite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Order_Opposite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Order_Opposite(builtin);
}

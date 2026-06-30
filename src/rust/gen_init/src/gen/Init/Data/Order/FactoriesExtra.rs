// Lean compiler output
// Module: Init.Data.Order.FactoriesExtra
// Imports: Init.Data.Order.ClassesExtra Init.Data.Order.Ord Init.Data.Order.Classes Init.Data.Bool
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Ord::Basic::l_instDecidableEqOrdering;
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Data::Order::ClassesExtra::{
    initialize_Init_Data_Order_ClassesExtra, runtime_initialize_Init_Data_Order_ClassesExtra,
};
use crate::r#gen::Init::Data::Order::Ord::{
    initialize_Init_Data_Order_Ord, runtime_initialize_Init_Data_Order_Ord,
};
pub unsafe fn l_LE_ofOrd(
    mut v_00_u03b1_94_: *mut leanh::LeanObject,
    mut v_inst_95_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = leanh::lean_box(0);
    return v___x_96_;
}
pub unsafe fn l_LE_ofOrd___boxed(
    mut v_00_u03b1_97_: *mut leanh::LeanObject,
    mut v_inst_98_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_99_ = l_LE_ofOrd(v_00_u03b1_97_, v_inst_98_);
    leanh::lean_dec_ref(v_inst_98_);
    return v_res_99_;
}
pub unsafe fn l_DecidableLE_ofOrd___redArg(
    mut v_inst_100_: *mut leanh::LeanObject,
    mut v_a_101_: *mut leanh::LeanObject,
    mut v_b_102_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: u8 = 0;
    v___x_103_ = leanh::lean_apply_2(v_inst_100_, v_a_101_, v_b_102_);
    v___x_104_ = (leanh::lean_unbox(v___x_103_) as u8);
    if v___x_104_ == 2 {
        let mut v___x_105_: u8 = 0;
        v___x_105_ = 0;
        return v___x_105_;
    } else {
        let mut v___x_106_: u8 = 0;
        v___x_106_ = 1;
        return v___x_106_;
    }
}
pub unsafe fn l_DecidableLE_ofOrd___redArg___boxed(
    mut v_inst_107_: *mut leanh::LeanObject,
    mut v_a_108_: *mut leanh::LeanObject,
    mut v_b_109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_110_: u8 = 0;
    let mut v_r_111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_110_ = l_DecidableLE_ofOrd___redArg(v_inst_107_, v_a_108_, v_b_109_);
    v_r_111_ = leanh::lean_box((v_res_110_) as usize);
    return v_r_111_;
}
pub unsafe fn l_DecidableLE_ofOrd(
    mut v_00_u03b1_112_: *mut leanh::LeanObject,
    mut v_inst_113_: *mut leanh::LeanObject,
    mut v_inst_114_: *mut leanh::LeanObject,
    mut v_inst_115_: *mut leanh::LeanObject,
    mut v_a_116_: *mut leanh::LeanObject,
    mut v_b_117_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: u8 = 0;
    v___x_118_ = leanh::lean_apply_2(v_inst_114_, v_a_116_, v_b_117_);
    v___x_119_ = (leanh::lean_unbox(v___x_118_) as u8);
    if v___x_119_ == 2 {
        let mut v___x_120_: u8 = 0;
        v___x_120_ = 0;
        return v___x_120_;
    } else {
        let mut v___x_121_: u8 = 0;
        v___x_121_ = 1;
        return v___x_121_;
    }
}
pub unsafe fn l_DecidableLE_ofOrd___boxed(
    mut v_00_u03b1_122_: *mut leanh::LeanObject,
    mut v_inst_123_: *mut leanh::LeanObject,
    mut v_inst_124_: *mut leanh::LeanObject,
    mut v_inst_125_: *mut leanh::LeanObject,
    mut v_a_126_: *mut leanh::LeanObject,
    mut v_b_127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_128_: u8 = 0;
    let mut v_r_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_128_ = l_DecidableLE_ofOrd(
        v_00_u03b1_122_,
        v_inst_123_,
        v_inst_124_,
        v_inst_125_,
        v_a_126_,
        v_b_127_,
    );
    v_r_129_ = leanh::lean_box((v_res_128_) as usize);
    return v_r_129_;
}
pub unsafe fn l_LT_ofOrd(
    mut v_00_u03b1_130_: *mut leanh::LeanObject,
    mut v_inst_131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_132_ = leanh::lean_box(0);
    return v___x_132_;
}
pub unsafe fn l_LT_ofOrd___boxed(
    mut v_00_u03b1_133_: *mut leanh::LeanObject,
    mut v_inst_134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_135_ = l_LT_ofOrd(v_00_u03b1_133_, v_inst_134_);
    leanh::lean_dec_ref(v_inst_134_);
    return v_res_135_;
}
pub unsafe fn l_DecidableLT_ofOrd___redArg(
    mut v_inst_136_: *mut leanh::LeanObject,
    mut v_a_137_: *mut leanh::LeanObject,
    mut v_b_138_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: u8 = 0;
    let mut v___x_141_: u8 = 0;
    let mut v___x_142_: u8 = 0;
    v___x_139_ = leanh::lean_apply_2(v_inst_136_, v_a_137_, v_b_138_);
    v___x_140_ = 0;
    v___x_141_ = (leanh::lean_unbox(v___x_139_) as u8);
    v___x_142_ = l_instDecidableEqOrdering(v___x_141_, v___x_140_);
    return v___x_142_;
}
pub unsafe fn l_DecidableLT_ofOrd___redArg___boxed(
    mut v_inst_143_: *mut leanh::LeanObject,
    mut v_a_144_: *mut leanh::LeanObject,
    mut v_b_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_146_: u8 = 0;
    let mut v_r_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_146_ = l_DecidableLT_ofOrd___redArg(v_inst_143_, v_a_144_, v_b_145_);
    v_r_147_ = leanh::lean_box((v_res_146_) as usize);
    return v_r_147_;
}
pub unsafe fn l_DecidableLT_ofOrd(
    mut v_00_u03b1_148_: *mut leanh::LeanObject,
    mut v_inst_149_: *mut leanh::LeanObject,
    mut v_inst_150_: *mut leanh::LeanObject,
    mut v_inst_151_: *mut leanh::LeanObject,
    mut v_inst_152_: *mut leanh::LeanObject,
    mut v_inst_153_: *mut leanh::LeanObject,
    mut v_a_154_: *mut leanh::LeanObject,
    mut v_b_155_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: u8 = 0;
    let mut v___x_158_: u8 = 0;
    let mut v___x_159_: u8 = 0;
    v___x_156_ = leanh::lean_apply_2(v_inst_151_, v_a_154_, v_b_155_);
    v___x_157_ = 0;
    v___x_158_ = (leanh::lean_unbox(v___x_156_) as u8);
    v___x_159_ = l_instDecidableEqOrdering(v___x_158_, v___x_157_);
    return v___x_159_;
}
pub unsafe fn l_DecidableLT_ofOrd___boxed(
    mut v_00_u03b1_160_: *mut leanh::LeanObject,
    mut v_inst_161_: *mut leanh::LeanObject,
    mut v_inst_162_: *mut leanh::LeanObject,
    mut v_inst_163_: *mut leanh::LeanObject,
    mut v_inst_164_: *mut leanh::LeanObject,
    mut v_inst_165_: *mut leanh::LeanObject,
    mut v_a_166_: *mut leanh::LeanObject,
    mut v_b_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_168_: u8 = 0;
    let mut v_r_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_168_ = l_DecidableLT_ofOrd(
        v_00_u03b1_160_,
        v_inst_161_,
        v_inst_162_,
        v_inst_163_,
        v_inst_164_,
        v_inst_165_,
        v_a_166_,
        v_b_167_,
    );
    v_r_169_ = leanh::lean_box((v_res_168_) as usize);
    return v_r_169_;
}
pub unsafe fn l_BEq_ofOrd___redArg___lam__0(
    mut v_inst_170_: *mut leanh::LeanObject,
    mut v_a_171_: *mut leanh::LeanObject,
    mut v_b_172_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: u8 = 0;
    let mut v___x_175_: u8 = 0;
    let mut v___x_176_: u8 = 0;
    v___x_173_ = leanh::lean_apply_2(v_inst_170_, v_a_171_, v_b_172_);
    v___x_174_ = 1;
    v___x_175_ = (leanh::lean_unbox(v___x_173_) as u8);
    v___x_176_ = l_instDecidableEqOrdering(v___x_175_, v___x_174_);
    return v___x_176_;
}
pub unsafe fn l_BEq_ofOrd___redArg___lam__0___boxed(
    mut v_inst_177_: *mut leanh::LeanObject,
    mut v_a_178_: *mut leanh::LeanObject,
    mut v_b_179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_180_: u8 = 0;
    let mut v_r_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ = l_BEq_ofOrd___redArg___lam__0(v_inst_177_, v_a_178_, v_b_179_);
    v_r_181_ = leanh::lean_box((v_res_180_) as usize);
    return v_r_181_;
}
pub unsafe fn l_BEq_ofOrd___redArg(
    mut v_inst_182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_183_ = leanh::lean_alloc_closure(
        l_BEq_ofOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_183_, 0, v_inst_182_);
    return v___f_183_;
}
pub unsafe fn l_BEq_ofOrd(
    mut v_00_u03b1_184_: *mut leanh::LeanObject,
    mut v_inst_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_186_ = leanh::lean_alloc_closure(
        l_BEq_ofOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_186_, 0, v_inst_185_);
    return v___f_186_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Order_FactoriesExtra(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_ClassesExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Ord(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Order_FactoriesExtra(
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
pub unsafe fn initialize_Init_Data_Order_FactoriesExtra(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_ClassesExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Ord(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_FactoriesExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Order_FactoriesExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Order_FactoriesExtra(builtin);
}
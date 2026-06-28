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
    mut v_00_u03b1_94_: *mut crate::leanh::LeanObject,
    mut v_inst_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = crate::leanh::lean_box(0);
    return v___x_96_;
}
pub unsafe fn l_LE_ofOrd___boxed(
    mut v_00_u03b1_97_: *mut crate::leanh::LeanObject,
    mut v_inst_98_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_99_ = l_LE_ofOrd(v_00_u03b1_97_, v_inst_98_);
    crate::leanh::lean_dec_ref(v_inst_98_);
    return v_res_99_;
}
pub unsafe fn l_DecidableLE_ofOrd___redArg(
    mut v_inst_100_: *mut crate::leanh::LeanObject,
    mut v_a_101_: *mut crate::leanh::LeanObject,
    mut v_b_102_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: u8 = 0;
    v___x_103_ = crate::leanh::lean_apply_2(v_inst_100_, v_a_101_, v_b_102_);
    v___x_104_ = (crate::leanh::lean_unbox(v___x_103_) as u8);
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
    mut v_inst_107_: *mut crate::leanh::LeanObject,
    mut v_a_108_: *mut crate::leanh::LeanObject,
    mut v_b_109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_110_: u8 = 0;
    let mut v_r_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_110_ = l_DecidableLE_ofOrd___redArg(v_inst_107_, v_a_108_, v_b_109_);
    v_r_111_ = crate::leanh::lean_box((v_res_110_) as usize);
    return v_r_111_;
}
pub unsafe fn l_DecidableLE_ofOrd(
    mut v_00_u03b1_112_: *mut crate::leanh::LeanObject,
    mut v_inst_113_: *mut crate::leanh::LeanObject,
    mut v_inst_114_: *mut crate::leanh::LeanObject,
    mut v_inst_115_: *mut crate::leanh::LeanObject,
    mut v_a_116_: *mut crate::leanh::LeanObject,
    mut v_b_117_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: u8 = 0;
    v___x_118_ = crate::leanh::lean_apply_2(v_inst_114_, v_a_116_, v_b_117_);
    v___x_119_ = (crate::leanh::lean_unbox(v___x_118_) as u8);
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
    mut v_00_u03b1_122_: *mut crate::leanh::LeanObject,
    mut v_inst_123_: *mut crate::leanh::LeanObject,
    mut v_inst_124_: *mut crate::leanh::LeanObject,
    mut v_inst_125_: *mut crate::leanh::LeanObject,
    mut v_a_126_: *mut crate::leanh::LeanObject,
    mut v_b_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_128_: u8 = 0;
    let mut v_r_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_128_ = l_DecidableLE_ofOrd(
        v_00_u03b1_122_,
        v_inst_123_,
        v_inst_124_,
        v_inst_125_,
        v_a_126_,
        v_b_127_,
    );
    v_r_129_ = crate::leanh::lean_box((v_res_128_) as usize);
    return v_r_129_;
}
pub unsafe fn l_LT_ofOrd(
    mut v_00_u03b1_130_: *mut crate::leanh::LeanObject,
    mut v_inst_131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_132_ = crate::leanh::lean_box(0);
    return v___x_132_;
}
pub unsafe fn l_LT_ofOrd___boxed(
    mut v_00_u03b1_133_: *mut crate::leanh::LeanObject,
    mut v_inst_134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_135_ = l_LT_ofOrd(v_00_u03b1_133_, v_inst_134_);
    crate::leanh::lean_dec_ref(v_inst_134_);
    return v_res_135_;
}
pub unsafe fn l_DecidableLT_ofOrd___redArg(
    mut v_inst_136_: *mut crate::leanh::LeanObject,
    mut v_a_137_: *mut crate::leanh::LeanObject,
    mut v_b_138_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: u8 = 0;
    let mut v___x_141_: u8 = 0;
    let mut v___x_142_: u8 = 0;
    v___x_139_ = crate::leanh::lean_apply_2(v_inst_136_, v_a_137_, v_b_138_);
    v___x_140_ = 0;
    v___x_141_ = (crate::leanh::lean_unbox(v___x_139_) as u8);
    v___x_142_ = l_instDecidableEqOrdering(v___x_141_, v___x_140_);
    return v___x_142_;
}
pub unsafe fn l_DecidableLT_ofOrd___redArg___boxed(
    mut v_inst_143_: *mut crate::leanh::LeanObject,
    mut v_a_144_: *mut crate::leanh::LeanObject,
    mut v_b_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_146_: u8 = 0;
    let mut v_r_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_146_ = l_DecidableLT_ofOrd___redArg(v_inst_143_, v_a_144_, v_b_145_);
    v_r_147_ = crate::leanh::lean_box((v_res_146_) as usize);
    return v_r_147_;
}
pub unsafe fn l_DecidableLT_ofOrd(
    mut v_00_u03b1_148_: *mut crate::leanh::LeanObject,
    mut v_inst_149_: *mut crate::leanh::LeanObject,
    mut v_inst_150_: *mut crate::leanh::LeanObject,
    mut v_inst_151_: *mut crate::leanh::LeanObject,
    mut v_inst_152_: *mut crate::leanh::LeanObject,
    mut v_inst_153_: *mut crate::leanh::LeanObject,
    mut v_a_154_: *mut crate::leanh::LeanObject,
    mut v_b_155_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: u8 = 0;
    let mut v___x_158_: u8 = 0;
    let mut v___x_159_: u8 = 0;
    v___x_156_ = crate::leanh::lean_apply_2(v_inst_151_, v_a_154_, v_b_155_);
    v___x_157_ = 0;
    v___x_158_ = (crate::leanh::lean_unbox(v___x_156_) as u8);
    v___x_159_ = l_instDecidableEqOrdering(v___x_158_, v___x_157_);
    return v___x_159_;
}
pub unsafe fn l_DecidableLT_ofOrd___boxed(
    mut v_00_u03b1_160_: *mut crate::leanh::LeanObject,
    mut v_inst_161_: *mut crate::leanh::LeanObject,
    mut v_inst_162_: *mut crate::leanh::LeanObject,
    mut v_inst_163_: *mut crate::leanh::LeanObject,
    mut v_inst_164_: *mut crate::leanh::LeanObject,
    mut v_inst_165_: *mut crate::leanh::LeanObject,
    mut v_a_166_: *mut crate::leanh::LeanObject,
    mut v_b_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_168_: u8 = 0;
    let mut v_r_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    v_r_169_ = crate::leanh::lean_box((v_res_168_) as usize);
    return v_r_169_;
}
pub unsafe fn l_BEq_ofOrd___redArg___lam__0(
    mut v_inst_170_: *mut crate::leanh::LeanObject,
    mut v_a_171_: *mut crate::leanh::LeanObject,
    mut v_b_172_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: u8 = 0;
    let mut v___x_175_: u8 = 0;
    let mut v___x_176_: u8 = 0;
    v___x_173_ = crate::leanh::lean_apply_2(v_inst_170_, v_a_171_, v_b_172_);
    v___x_174_ = 1;
    v___x_175_ = (crate::leanh::lean_unbox(v___x_173_) as u8);
    v___x_176_ = l_instDecidableEqOrdering(v___x_175_, v___x_174_);
    return v___x_176_;
}
pub unsafe fn l_BEq_ofOrd___redArg___lam__0___boxed(
    mut v_inst_177_: *mut crate::leanh::LeanObject,
    mut v_a_178_: *mut crate::leanh::LeanObject,
    mut v_b_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_180_: u8 = 0;
    let mut v_r_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ = l_BEq_ofOrd___redArg___lam__0(v_inst_177_, v_a_178_, v_b_179_);
    v_r_181_ = crate::leanh::lean_box((v_res_180_) as usize);
    return v_r_181_;
}
pub unsafe fn l_BEq_ofOrd___redArg(
    mut v_inst_182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_183_ = crate::leanh::lean_alloc_closure(
        l_BEq_ofOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_183_, 0, v_inst_182_);
    return v___f_183_;
}
pub unsafe fn l_BEq_ofOrd(
    mut v_00_u03b1_184_: *mut crate::leanh::LeanObject,
    mut v_inst_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_186_ = crate::leanh::lean_alloc_closure(
        l_BEq_ofOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_186_, 0, v_inst_185_);
    return v___f_186_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Order_FactoriesExtra(
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
    res = runtime_initialize_Init_Data_Order_Ord(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Order_FactoriesExtra(
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
pub unsafe fn initialize_Init_Data_Order_FactoriesExtra(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_Data_Order_Ord(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_FactoriesExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Order_FactoriesExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Order_FactoriesExtra(builtin);
}

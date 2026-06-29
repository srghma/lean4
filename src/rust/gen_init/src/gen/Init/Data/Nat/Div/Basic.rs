// Lean compiler output
// Module: Init.Data.Nat.Div.Basic
// Imports: Init.Data.NeZero Init.WF Init.MetaTypes Init.WFTactics
use crate::ffi::{
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div_exact, lean_nat_sub,
};
use crate::r#gen::Init::Data::NeZero::{
    initialize_Init_Data_NeZero, runtime_initialize_Init_Data_NeZero,
};
use crate::r#gen::Init::MetaTypes::{initialize_Init_MetaTypes, runtime_initialize_Init_MetaTypes};
use crate::r#gen::Init::WF::{initialize_Init_WF, runtime_initialize_Init_WF};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
pub static mut l_Nat_instDvd: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Nat_instDvd() -> *mut crate::leanh::LeanObject {
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = crate::leanh::lean_box(0);
    return v___x_96_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(
    mut v_fuel_97_: *mut crate::leanh::LeanObject,
    mut v_h__1_98_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_100_: u8 = 0;
    let mut v_one_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zero_99_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_100_ = lean_nat_dec_eq(v_fuel_97_, v_zero_99_);
    v_one_101_ = crate::leanh::lean_unsigned_to_nat(1);
    v_n_102_ = lean_nat_sub(v_fuel_97_, v_one_101_);
    v___x_103_ = crate::leanh::lean_apply_2(v_h__1_98_, v_n_102_, crate::leanh::lean_box(0));
    return v___x_103_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg___boxed(
    mut v_fuel_104_: *mut crate::leanh::LeanObject,
    mut v_h__1_105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_106_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(
        v_fuel_104_,
        v_h__1_105_,
    );
    crate::leanh::lean_dec(v_fuel_104_);
    return v_res_106_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(
    mut v_x_107_: *mut crate::leanh::LeanObject,
    mut v_motive_108_: *mut crate::leanh::LeanObject,
    mut v_fuel_109_: *mut crate::leanh::LeanObject,
    mut v_hfuel_110_: *mut crate::leanh::LeanObject,
    mut v_h__1_111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_113_: u8 = 0;
    let mut v_one_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zero_112_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_113_ = lean_nat_dec_eq(v_fuel_109_, v_zero_112_);
    v_one_114_ = crate::leanh::lean_unsigned_to_nat(1);
    v_n_115_ = lean_nat_sub(v_fuel_109_, v_one_114_);
    v___x_116_ = crate::leanh::lean_apply_2(v_h__1_111_, v_n_115_, crate::leanh::lean_box(0));
    return v___x_116_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___boxed(
    mut v_x_117_: *mut crate::leanh::LeanObject,
    mut v_motive_118_: *mut crate::leanh::LeanObject,
    mut v_fuel_119_: *mut crate::leanh::LeanObject,
    mut v_hfuel_120_: *mut crate::leanh::LeanObject,
    mut v_h__1_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(
        v_x_117_,
        v_motive_118_,
        v_fuel_119_,
        v_hfuel_120_,
        v_h__1_121_,
    );
    crate::leanh::lean_dec(v_fuel_119_);
    crate::leanh::lean_dec(v_x_117_);
    return v_res_122_;
}
pub unsafe fn l_Nat_div_inductionOn___redArg(
    mut v_x_123_: *mut crate::leanh::LeanObject,
    mut v_y_124_: *mut crate::leanh::LeanObject,
    mut v_ind_125_: *mut crate::leanh::LeanObject,
    mut v_base_126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: u8 = 0;
    v___x_127_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_128_ = lean_nat_dec_lt(v___x_127_, v_y_124_);
    if v___x_128_ == 0 {
        let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_ind_125_);
        v___x_129_ =
            crate::leanh::lean_apply_3(v_base_126_, v_x_123_, v_y_124_, crate::leanh::lean_box(0));
        return v___x_129_;
    } else {
        let mut v___x_130_: u8 = 0;
        v___x_130_ = lean_nat_dec_le(v_y_124_, v_x_123_);
        if v___x_130_ == 0 {
            let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_ind_125_);
            v___x_131_ = crate::leanh::lean_apply_3(
                v_base_126_,
                v_x_123_,
                v_y_124_,
                crate::leanh::lean_box(0),
            );
            return v___x_131_;
        } else {
            let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_132_ = lean_nat_sub(v_x_123_, v_y_124_);
            crate::leanh::lean_inc(v_ind_125_);
            crate::leanh::lean_inc(v_y_124_);
            v___x_133_ =
                l_Nat_div_inductionOn___redArg(v___x_132_, v_y_124_, v_ind_125_, v_base_126_);
            v___x_134_ = crate::leanh::lean_apply_4(
                v_ind_125_,
                v_x_123_,
                v_y_124_,
                crate::leanh::lean_box(0),
                v___x_133_,
            );
            return v___x_134_;
        }
    }
}
pub unsafe fn l_Nat_div_inductionOn(
    mut v_motive_135_: *mut crate::leanh::LeanObject,
    mut v_x_136_: *mut crate::leanh::LeanObject,
    mut v_y_137_: *mut crate::leanh::LeanObject,
    mut v_ind_138_: *mut crate::leanh::LeanObject,
    mut v_base_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_140_ = l_Nat_div_inductionOn___redArg(v_x_136_, v_y_137_, v_ind_138_, v_base_139_);
    return v___x_140_;
}
pub unsafe fn l_Nat_divExact___boxed(
    mut v_x_144_: *mut crate::leanh::LeanObject,
    mut v_y_145_: *mut crate::leanh::LeanObject,
    mut v_h_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_147_ = lean_nat_div_exact(v_x_144_, v_y_145_);
    crate::leanh::lean_dec(v_y_145_);
    crate::leanh::lean_dec(v_x_144_);
    return v_res_147_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(
    mut v_x_148_: *mut crate::leanh::LeanObject,
    mut v_x_149_: *mut crate::leanh::LeanObject,
    mut v_h__1_150_: *mut crate::leanh::LeanObject,
    mut v_h__2_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_153_: u8 = 0;
    v_zero_152_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_153_ = lean_nat_dec_eq(v_x_148_, v_zero_152_);
    if v_isZero_153_ == 1 {
        let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_151_);
        v___x_154_ = crate::leanh::lean_apply_1(v_h__1_150_, v_x_149_);
        return v___x_154_;
    } else {
        let mut v_one_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_150_);
        v_one_155_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_156_ = lean_nat_sub(v_x_148_, v_one_155_);
        v___x_157_ = crate::leanh::lean_apply_2(v_h__2_151_, v_n_156_, v_x_149_);
        return v___x_157_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg___boxed(
    mut v_x_158_: *mut crate::leanh::LeanObject,
    mut v_x_159_: *mut crate::leanh::LeanObject,
    mut v_h__1_160_: *mut crate::leanh::LeanObject,
    mut v_h__2_161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_162_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(
        v_x_158_,
        v_x_159_,
        v_h__1_160_,
        v_h__2_161_,
    );
    crate::leanh::lean_dec(v_x_158_);
    return v_res_162_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(
    mut v_motive_163_: *mut crate::leanh::LeanObject,
    mut v_x_164_: *mut crate::leanh::LeanObject,
    mut v_x_165_: *mut crate::leanh::LeanObject,
    mut v_h__1_166_: *mut crate::leanh::LeanObject,
    mut v_h__2_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_169_: u8 = 0;
    v_zero_168_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_169_ = lean_nat_dec_eq(v_x_164_, v_zero_168_);
    if v_isZero_169_ == 1 {
        let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_167_);
        v___x_170_ = crate::leanh::lean_apply_1(v_h__1_166_, v_x_165_);
        return v___x_170_;
    } else {
        let mut v_one_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_166_);
        v_one_171_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_172_ = lean_nat_sub(v_x_164_, v_one_171_);
        v___x_173_ = crate::leanh::lean_apply_2(v_h__2_167_, v_n_172_, v_x_165_);
        return v___x_173_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___boxed(
    mut v_motive_174_: *mut crate::leanh::LeanObject,
    mut v_x_175_: *mut crate::leanh::LeanObject,
    mut v_x_176_: *mut crate::leanh::LeanObject,
    mut v_h__1_177_: *mut crate::leanh::LeanObject,
    mut v_h__2_178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_179_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(
        v_motive_174_,
        v_x_175_,
        v_x_176_,
        v_h__1_177_,
        v_h__2_178_,
    );
    crate::leanh::lean_dec(v_x_175_);
    return v_res_179_;
}
pub unsafe fn l_Nat_mod_inductionOn___redArg(
    mut v_x_180_: *mut crate::leanh::LeanObject,
    mut v_y_181_: *mut crate::leanh::LeanObject,
    mut v_ind_182_: *mut crate::leanh::LeanObject,
    mut v_base_183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_184_ = l_Nat_div_inductionOn___redArg(v_x_180_, v_y_181_, v_ind_182_, v_base_183_);
    return v___x_184_;
}
pub unsafe fn l_Nat_mod_inductionOn(
    mut v_motive_185_: *mut crate::leanh::LeanObject,
    mut v_x_186_: *mut crate::leanh::LeanObject,
    mut v_y_187_: *mut crate::leanh::LeanObject,
    mut v_ind_188_: *mut crate::leanh::LeanObject,
    mut v_base_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_190_ = l_Nat_div_inductionOn___redArg(v_x_186_, v_y_187_, v_ind_188_, v_base_189_);
    return v___x_190_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Div_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_NeZero(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Nat_instDvd = _init_l_Nat_instDvd();
    crate::leanh::lean_mark_persistent(l_Nat_instDvd);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Div_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_MetaTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Div_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_NeZero(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_MetaTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Div_Basic(builtin);
}

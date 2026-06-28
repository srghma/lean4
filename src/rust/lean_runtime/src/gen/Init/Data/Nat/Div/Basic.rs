// Lean compiler output
// Module: Init.Data.Nat.Div.Basic
// Imports: Init.Data.NeZero Init.WF Init.MetaTypes Init.WFTactics
use crate::r#gen::Init::Data::NeZero::{
    initialize_Init_Data_NeZero, runtime_initialize_Init_Data_NeZero,
};
use crate::r#gen::Init::MetaTypes::{initialize_Init_MetaTypes, meta_initialize_Init_MetaTypes};
use crate::r#gen::Init::WF::{initialize_Init_WF, runtime_initialize_Init_WF};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_apply_4,
    lean_box, lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_unsigned_to_nat,
};
pub static mut l_Nat_instDvd: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Nat_instDvd() -> *mut LeanObject {
    let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
    v___x_96_ = lean_box(0);
    return v___x_96_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(
    mut v_fuel_97_: *mut LeanObject,
    mut v_h__1_98_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_100_: u8 = 0;
    let mut v_one_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    v_zero_99_ = lean_unsigned_to_nat(0);
    v_isZero_100_ = lean_nat_dec_eq(v_fuel_97_, v_zero_99_);
    v_one_101_ = lean_unsigned_to_nat(1);
    v_n_102_ = lean_nat_sub(v_fuel_97_, v_one_101_);
    v___x_103_ = lean_apply_2(v_h__1_98_, v_n_102_, lean_box(0));
    return v___x_103_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg___boxed(
    mut v_fuel_104_: *mut LeanObject,
    mut v_h__1_105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_106_: *mut LeanObject = core::ptr::null_mut();
    v_res_106_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(
        v_fuel_104_,
        v_h__1_105_,
    );
    lean_dec(v_fuel_104_);
    return v_res_106_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(
    mut v_x_107_: *mut LeanObject,
    mut v_motive_108_: *mut LeanObject,
    mut v_fuel_109_: *mut LeanObject,
    mut v_hfuel_110_: *mut LeanObject,
    mut v_h__1_111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_113_: u8 = 0;
    let mut v_one_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
    v_zero_112_ = lean_unsigned_to_nat(0);
    v_isZero_113_ = lean_nat_dec_eq(v_fuel_109_, v_zero_112_);
    v_one_114_ = lean_unsigned_to_nat(1);
    v_n_115_ = lean_nat_sub(v_fuel_109_, v_one_114_);
    v___x_116_ = lean_apply_2(v_h__1_111_, v_n_115_, lean_box(0));
    return v___x_116_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___boxed(
    mut v_x_117_: *mut LeanObject,
    mut v_motive_118_: *mut LeanObject,
    mut v_fuel_119_: *mut LeanObject,
    mut v_hfuel_120_: *mut LeanObject,
    mut v_h__1_121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_122_: *mut LeanObject = core::ptr::null_mut();
    v_res_122_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(
        v_x_117_,
        v_motive_118_,
        v_fuel_119_,
        v_hfuel_120_,
        v_h__1_121_,
    );
    lean_dec(v_fuel_119_);
    lean_dec(v_x_117_);
    return v_res_122_;
}
pub unsafe fn l_Nat_div_inductionOn___redArg(
    mut v_x_123_: *mut LeanObject,
    mut v_y_124_: *mut LeanObject,
    mut v_ind_125_: *mut LeanObject,
    mut v_base_126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_128_: u8 = 0;
    v___x_127_ = lean_unsigned_to_nat(0);
    v___x_128_ = lean_nat_dec_lt(v___x_127_, v_y_124_);
    if v___x_128_ == 0 {
        let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_ind_125_);
        v___x_129_ = lean_apply_3(v_base_126_, v_x_123_, v_y_124_, lean_box(0));
        return v___x_129_;
    } else {
        let mut v___x_130_: u8 = 0;
        v___x_130_ = lean_nat_dec_le(v_y_124_, v_x_123_);
        if v___x_130_ == 0 {
            let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_ind_125_);
            v___x_131_ = lean_apply_3(v_base_126_, v_x_123_, v_y_124_, lean_box(0));
            return v___x_131_;
        } else {
            let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
            v___x_132_ = lean_nat_sub(v_x_123_, v_y_124_);
            lean_inc(v_ind_125_);
            lean_inc(v_y_124_);
            v___x_133_ =
                l_Nat_div_inductionOn___redArg(v___x_132_, v_y_124_, v_ind_125_, v_base_126_);
            v___x_134_ = lean_apply_4(v_ind_125_, v_x_123_, v_y_124_, lean_box(0), v___x_133_);
            return v___x_134_;
        }
    }
}
pub unsafe fn l_Nat_div_inductionOn(
    mut v_motive_135_: *mut LeanObject,
    mut v_x_136_: *mut LeanObject,
    mut v_y_137_: *mut LeanObject,
    mut v_ind_138_: *mut LeanObject,
    mut v_base_139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    v___x_140_ = l_Nat_div_inductionOn___redArg(v_x_136_, v_y_137_, v_ind_138_, v_base_139_);
    return v___x_140_;
}
pub unsafe fn l_Nat_divExact___boxed(
    mut v_x_144_: *mut LeanObject,
    mut v_y_145_: *mut LeanObject,
    mut v_h_146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_147_: *mut LeanObject = core::ptr::null_mut();
    v_res_147_ = lean_nat_div_exact(v_x_144_, v_y_145_);
    lean_dec(v_y_145_);
    lean_dec(v_x_144_);
    return v_res_147_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(
    mut v_x_148_: *mut LeanObject,
    mut v_x_149_: *mut LeanObject,
    mut v_h__1_150_: *mut LeanObject,
    mut v_h__2_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_153_: u8 = 0;
    v_zero_152_ = lean_unsigned_to_nat(0);
    v_isZero_153_ = lean_nat_dec_eq(v_x_148_, v_zero_152_);
    if v_isZero_153_ == 1 {
        let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_151_);
        v___x_154_ = lean_apply_1(v_h__1_150_, v_x_149_);
        return v___x_154_;
    } else {
        let mut v_one_155_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_150_);
        v_one_155_ = lean_unsigned_to_nat(1);
        v_n_156_ = lean_nat_sub(v_x_148_, v_one_155_);
        v___x_157_ = lean_apply_2(v_h__2_151_, v_n_156_, v_x_149_);
        return v___x_157_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg___boxed(
    mut v_x_158_: *mut LeanObject,
    mut v_x_159_: *mut LeanObject,
    mut v_h__1_160_: *mut LeanObject,
    mut v_h__2_161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_162_: *mut LeanObject = core::ptr::null_mut();
    v_res_162_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(
        v_x_158_,
        v_x_159_,
        v_h__1_160_,
        v_h__2_161_,
    );
    lean_dec(v_x_158_);
    return v_res_162_;
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(
    mut v_motive_163_: *mut LeanObject,
    mut v_x_164_: *mut LeanObject,
    mut v_x_165_: *mut LeanObject,
    mut v_h__1_166_: *mut LeanObject,
    mut v_h__2_167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_169_: u8 = 0;
    v_zero_168_ = lean_unsigned_to_nat(0);
    v_isZero_169_ = lean_nat_dec_eq(v_x_164_, v_zero_168_);
    if v_isZero_169_ == 1 {
        let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_167_);
        v___x_170_ = lean_apply_1(v_h__1_166_, v_x_165_);
        return v___x_170_;
    } else {
        let mut v_one_171_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_166_);
        v_one_171_ = lean_unsigned_to_nat(1);
        v_n_172_ = lean_nat_sub(v_x_164_, v_one_171_);
        v___x_173_ = lean_apply_2(v_h__2_167_, v_n_172_, v_x_165_);
        return v___x_173_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___boxed(
    mut v_motive_174_: *mut LeanObject,
    mut v_x_175_: *mut LeanObject,
    mut v_x_176_: *mut LeanObject,
    mut v_h__1_177_: *mut LeanObject,
    mut v_h__2_178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_179_: *mut LeanObject = core::ptr::null_mut();
    v_res_179_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(
        v_motive_174_,
        v_x_175_,
        v_x_176_,
        v_h__1_177_,
        v_h__2_178_,
    );
    lean_dec(v_x_175_);
    return v_res_179_;
}
pub unsafe fn l_Nat_mod_inductionOn___redArg(
    mut v_x_180_: *mut LeanObject,
    mut v_y_181_: *mut LeanObject,
    mut v_ind_182_: *mut LeanObject,
    mut v_base_183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    v___x_184_ = l_Nat_div_inductionOn___redArg(v_x_180_, v_y_181_, v_ind_182_, v_base_183_);
    return v___x_184_;
}
pub unsafe fn l_Nat_mod_inductionOn(
    mut v_motive_185_: *mut LeanObject,
    mut v_x_186_: *mut LeanObject,
    mut v_y_187_: *mut LeanObject,
    mut v_ind_188_: *mut LeanObject,
    mut v_base_189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    v___x_190_ = l_Nat_div_inductionOn___redArg(v_x_186_, v_y_187_, v_ind_188_, v_base_189_);
    return v___x_190_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Div_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_NeZero(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Nat_instDvd = _init_l_Nat_instDvd();
    lean_mark_persistent(l_Nat_instDvd);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Div_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_MetaTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Div_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_NeZero(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_MetaTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Nat_Div_Basic(builtin);
}

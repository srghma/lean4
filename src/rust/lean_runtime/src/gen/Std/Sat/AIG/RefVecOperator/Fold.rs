// Lean compiler output
// Module: Std.Sat.AIG.RefVecOperator.Fold
// Imports: Std.Sat.AIG.LawfulVecOperator Init.Omega
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::LawfulVecOperator::{
    initialize_Std_Sat_AIG_LawfulVecOperator, runtime_initialize_Std_Sat_AIG_LawfulVecOperator,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{lean_nat_land, lean_nat_shiftr};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_2, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub static l_Std_Sat_AIG_RefVec_fold___redArg___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            1 as *mut LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_RefVec_fold___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_RefVec_fold___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___redArg(
    mut v_aig_89_: *mut LeanObject,
    mut v_acc_90_: *mut LeanObject,
    mut v_idx_91_: *mut LeanObject,
    mut v_len_92_: *mut LeanObject,
    mut v_input_93_: *mut LeanObject,
    mut v_f_94_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_104_: u8 = 0;
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_111_: u8 = 0;
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_113_: u8 = 0;
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_104_ = lean_nat_dec_lt(v_idx_91_, v_len_92_);
                if v___x_104_ == 0 {
                    lean_dec_ref(v_f_94_);
                    lean_dec(v_idx_91_);
                    v___x_105_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_105_, 0, v_aig_89_);
                    lean_ctor_set(v___x_105_, 1, v_acc_90_);
                    return v___x_105_;
                } else {
                    v_ref_106_ = lean_array_fget_borrowed(v_input_93_, v_idx_91_);
                    v___x_107_ = lean_unsigned_to_nat(1);
                    v___x_108_ = lean_nat_shiftr(v_ref_106_, v___x_107_);
                    v___x_109_ = lean_nat_land(v___x_107_, v_ref_106_);
                    v___x_110_ = lean_unsigned_to_nat(0);
                    v___x_111_ = lean_nat_dec_eq(v___x_109_, v___x_110_);
                    lean_dec(v___x_109_);
                    if v___x_111_ == 0 {
                        v___x_112_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_112_, 0, v___x_108_);
                        lean_ctor_set_uint8(
                            v___x_112_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_104_,
                        );
                        v___y_96_ = v___x_112_;
                        state = 1;
                        continue;
                    } else {
                        v___x_113_ = 0;
                        v___x_114_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_114_, 0, v___x_108_);
                        lean_ctor_set_uint8(
                            v___x_114_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_113_,
                        );
                        v___y_96_ = v___x_114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_97_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_97_, 0, v_acc_90_);
                lean_ctor_set(v___x_97_, 1, v___y_96_);
                lean_inc_ref(v_f_94_);
                v_res_98_ = lean_apply_2(v_f_94_, v_aig_89_, v___x_97_);
                v_aig_99_ = lean_ctor_get(v_res_98_, 0);
                lean_inc_ref(v_aig_99_);
                v_ref_100_ = lean_ctor_get(v_res_98_, 1);
                lean_inc_ref(v_ref_100_);
                lean_dec_ref(v_res_98_);
                v___x_101_ = lean_unsigned_to_nat(1);
                v___x_102_ = lean_nat_add(v_idx_91_, v___x_101_);
                lean_dec(v_idx_91_);
                v_aig_89_ = v_aig_99_;
                v_acc_90_ = v_ref_100_;
                v_idx_91_ = v___x_102_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___redArg___boxed(
    mut v_aig_115_: *mut LeanObject,
    mut v_acc_116_: *mut LeanObject,
    mut v_idx_117_: *mut LeanObject,
    mut v_len_118_: *mut LeanObject,
    mut v_input_119_: *mut LeanObject,
    mut v_f_120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_121_: *mut LeanObject = core::ptr::null_mut();
    v_res_121_ = l_Std_Sat_AIG_RefVec_fold_go___redArg(
        v_aig_115_,
        v_acc_116_,
        v_idx_117_,
        v_len_118_,
        v_input_119_,
        v_f_120_,
    );
    lean_dec_ref(v_input_119_);
    lean_dec(v_len_118_);
    return v_res_121_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go(
    mut v_00_u03b1_122_: *mut LeanObject,
    mut v_inst_123_: *mut LeanObject,
    mut v_inst_124_: *mut LeanObject,
    mut v_aig_125_: *mut LeanObject,
    mut v_acc_126_: *mut LeanObject,
    mut v_idx_127_: *mut LeanObject,
    mut v_len_128_: *mut LeanObject,
    mut v_input_129_: *mut LeanObject,
    mut v_f_130_: *mut LeanObject,
    mut v_inst_131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    v___x_132_ = l_Std_Sat_AIG_RefVec_fold_go___redArg(
        v_aig_125_,
        v_acc_126_,
        v_idx_127_,
        v_len_128_,
        v_input_129_,
        v_f_130_,
    );
    return v___x_132_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold_go___boxed(
    mut v_00_u03b1_133_: *mut LeanObject,
    mut v_inst_134_: *mut LeanObject,
    mut v_inst_135_: *mut LeanObject,
    mut v_aig_136_: *mut LeanObject,
    mut v_acc_137_: *mut LeanObject,
    mut v_idx_138_: *mut LeanObject,
    mut v_len_139_: *mut LeanObject,
    mut v_input_140_: *mut LeanObject,
    mut v_f_141_: *mut LeanObject,
    mut v_inst_142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_143_: *mut LeanObject = core::ptr::null_mut();
    v_res_143_ = l_Std_Sat_AIG_RefVec_fold_go(
        v_00_u03b1_133_,
        v_inst_134_,
        v_inst_135_,
        v_aig_136_,
        v_acc_137_,
        v_idx_138_,
        v_len_139_,
        v_input_140_,
        v_f_141_,
        v_inst_142_,
    );
    lean_dec_ref(v_input_140_);
    lean_dec(v_len_139_);
    lean_dec_ref(v_inst_135_);
    lean_dec_ref(v_inst_134_);
    return v_res_143_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___redArg(
    mut v_len_147_: *mut LeanObject,
    mut v_aig_148_: *mut LeanObject,
    mut v_vec_149_: *mut LeanObject,
    mut v_func_150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    v___x_151_ = lean_unsigned_to_nat(0);
    v_acc_152_ = l_Std_Sat_AIG_RefVec_fold___redArg___closed__0;
    v___x_153_ = l_Std_Sat_AIG_RefVec_fold_go___redArg(
        v_aig_148_,
        v_acc_152_,
        v___x_151_,
        v_len_147_,
        v_vec_149_,
        v_func_150_,
    );
    return v___x_153_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___redArg___boxed(
    mut v_len_154_: *mut LeanObject,
    mut v_aig_155_: *mut LeanObject,
    mut v_vec_156_: *mut LeanObject,
    mut v_func_157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_158_: *mut LeanObject = core::ptr::null_mut();
    v_res_158_ =
        l_Std_Sat_AIG_RefVec_fold___redArg(v_len_154_, v_aig_155_, v_vec_156_, v_func_157_);
    lean_dec_ref(v_vec_156_);
    lean_dec(v_len_154_);
    return v_res_158_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold(
    mut v_00_u03b1_159_: *mut LeanObject,
    mut v_inst_160_: *mut LeanObject,
    mut v_inst_161_: *mut LeanObject,
    mut v_len_162_: *mut LeanObject,
    mut v_aig_163_: *mut LeanObject,
    mut v_vec_164_: *mut LeanObject,
    mut v_func_165_: *mut LeanObject,
    mut v_inst_166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    v___x_167_ =
        l_Std_Sat_AIG_RefVec_fold___redArg(v_len_162_, v_aig_163_, v_vec_164_, v_func_165_);
    return v___x_167_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_fold___boxed(
    mut v_00_u03b1_168_: *mut LeanObject,
    mut v_inst_169_: *mut LeanObject,
    mut v_inst_170_: *mut LeanObject,
    mut v_len_171_: *mut LeanObject,
    mut v_aig_172_: *mut LeanObject,
    mut v_vec_173_: *mut LeanObject,
    mut v_func_174_: *mut LeanObject,
    mut v_inst_175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_176_: *mut LeanObject = core::ptr::null_mut();
    v_res_176_ = l_Std_Sat_AIG_RefVec_fold(
        v_00_u03b1_168_,
        v_inst_169_,
        v_inst_170_,
        v_len_171_,
        v_aig_172_,
        v_vec_173_,
        v_func_174_,
        v_inst_175_,
    );
    lean_dec_ref(v_vec_173_);
    lean_dec(v_len_171_);
    lean_dec_ref(v_inst_170_);
    lean_dec_ref(v_inst_169_);
    return v_res_176_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_RefVecOperator_Fold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_RefVecOperator_Fold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_RefVecOperator_Fold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_RefVecOperator_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_RefVecOperator_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sat_AIG_RefVecOperator_Fold(builtin);
}

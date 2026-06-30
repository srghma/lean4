// Lean compiler output
// Module: Lean.Util.FindExpr
// Imports: Lean.Expr
use crate::ffi::{lean_expr_eqv, lean_find_expr, lean_find_ext_expr};
use crate::r#gen::Lean::Expr::{initialize_Lean_Expr, runtime_initialize_Lean_Expr};
pub unsafe fn l_Lean_Expr_findImpl_x3f___boxed(
    mut v_p_108_: *mut leanh::LeanObject,
    mut v_e_109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_110_ = lean_find_expr(v_p_108_, v_e_109_);
    leanh::lean_dec_ref(v_e_109_);
    leanh::lean_dec_ref(v_p_108_);
    return v_res_110_;
}
pub unsafe fn l_Lean_Expr_find_x3f(
    mut v_p_111_: *mut leanh::LeanObject,
    mut v_e_112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_113_ = lean_find_expr(v_p_111_, v_e_112_);
    return v___x_113_;
}
pub unsafe fn l_Lean_Expr_find_x3f___boxed(
    mut v_p_114_: *mut leanh::LeanObject,
    mut v_e_115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_116_ = l_Lean_Expr_find_x3f(v_p_114_, v_e_115_);
    leanh::lean_dec_ref(v_e_115_);
    leanh::lean_dec_ref(v_p_114_);
    return v_res_116_;
}
pub unsafe fn l_Lean_Expr_occurs___lam__0(
    mut v_e_117_: *mut leanh::LeanObject,
    mut v_s_118_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_119_: u8 = 0;
    v___x_119_ = lean_expr_eqv(v_s_118_, v_e_117_);
    return v___x_119_;
}
pub unsafe fn l_Lean_Expr_occurs___lam__0___boxed(
    mut v_e_120_: *mut leanh::LeanObject,
    mut v_s_121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_122_: u8 = 0;
    let mut v_r_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ = l_Lean_Expr_occurs___lam__0(v_e_120_, v_s_121_);
    leanh::lean_dec_ref(v_s_121_);
    leanh::lean_dec_ref(v_e_120_);
    v_r_123_ = leanh::lean_box((v_res_122_) as usize);
    return v_r_123_;
}
pub unsafe fn l_Lean_Expr_occurs(
    mut v_e_124_: *mut leanh::LeanObject,
    mut v_t_125_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_126_ = leanh::lean_alloc_closure(
        l_Lean_Expr_occurs___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_126_, 0, v_e_124_);
    v___x_127_ = lean_find_expr(v___f_126_, v_t_125_);
    leanh::lean_dec_ref(v___f_126_);
    if leanh::lean_obj_tag(v___x_127_) == 0 {
        let mut v___x_128_: u8 = 0;
        v___x_128_ = 0;
        return v___x_128_;
    } else {
        let mut v___x_129_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_127_, 1);
        v___x_129_ = 1;
        return v___x_129_;
    }
}
pub unsafe fn l_Lean_Expr_occurs___boxed(
    mut v_e_130_: *mut leanh::LeanObject,
    mut v_t_131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_132_: u8 = 0;
    let mut v_r_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_132_ = l_Lean_Expr_occurs(v_e_130_, v_t_131_);
    leanh::lean_dec_ref(v_t_131_);
    v_r_133_ = leanh::lean_box((v_res_132_) as usize);
    return v_r_133_;
}
pub unsafe fn l_Lean_Expr_FindStep_ctorIdx(mut v_x_134_: u8) -> *mut leanh::LeanObject {
    match v_x_134_ {
        0 => {
            let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_135_ = leanh::lean_unsigned_to_nat(0);
            return v___x_135_;
        }
        1 => {
            let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_136_ = leanh::lean_unsigned_to_nat(1);
            return v___x_136_;
        }
        _ => {
            let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_137_ = leanh::lean_unsigned_to_nat(2);
            return v___x_137_;
        }
    }
}
pub unsafe fn l_Lean_Expr_FindStep_ctorIdx___boxed(
    mut v_x_138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_139_: u8 = 0;
    let mut v_res_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_139_ = (leanh::lean_unbox(v_x_138_) as u8);
    v_res_140_ = l_Lean_Expr_FindStep_ctorIdx(v_x_boxed_139_);
    return v_res_140_;
}
pub unsafe fn l_Lean_Expr_FindStep_toCtorIdx(mut v_x_141_: u8) -> *mut leanh::LeanObject {
    let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = l_Lean_Expr_FindStep_ctorIdx(v_x_141_);
    return v___x_142_;
}
pub unsafe fn l_Lean_Expr_FindStep_toCtorIdx___boxed(
    mut v_x_143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_144_: u8 = 0;
    let mut v_res_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_144_ = (leanh::lean_unbox(v_x_143_) as u8);
    v_res_145_ = l_Lean_Expr_FindStep_toCtorIdx(v_x_4__boxed_144_);
    return v_res_145_;
}
pub unsafe fn l_Lean_Expr_FindStep_ctorElim___redArg(
    mut v_k_146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_146_);
    return v_k_146_;
}
pub unsafe fn l_Lean_Expr_FindStep_ctorElim___redArg___boxed(
    mut v_k_147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_148_ = l_Lean_Expr_FindStep_ctorElim___redArg(v_k_147_);
    leanh::lean_dec(v_k_147_);
    return v_res_148_;
}
pub unsafe fn l_Lean_Expr_FindStep_ctorElim(
    mut v_motive_149_: *mut leanh::LeanObject,
    mut v_ctorIdx_150_: *mut leanh::LeanObject,
    mut v_t_151_: u8,
    mut v_h_152_: *mut leanh::LeanObject,
    mut v_k_153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_153_);
    return v_k_153_;
}
pub unsafe fn l_Lean_Expr_FindStep_ctorElim___boxed(
    mut v_motive_154_: *mut leanh::LeanObject,
    mut v_ctorIdx_155_: *mut leanh::LeanObject,
    mut v_t_156_: *mut leanh::LeanObject,
    mut v_h_157_: *mut leanh::LeanObject,
    mut v_k_158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_159_: u8 = 0;
    let mut v_res_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_159_ = (leanh::lean_unbox(v_t_156_) as u8);
    v_res_160_ = l_Lean_Expr_FindStep_ctorElim(
        v_motive_154_,
        v_ctorIdx_155_,
        v_t_boxed_159_,
        v_h_157_,
        v_k_158_,
    );
    leanh::lean_dec(v_k_158_);
    leanh::lean_dec(v_ctorIdx_155_);
    return v_res_160_;
}
pub unsafe fn l_Lean_Expr_FindStep_found_elim___redArg(
    mut v_found_161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_found_161_);
    return v_found_161_;
}
pub unsafe fn l_Lean_Expr_FindStep_found_elim___redArg___boxed(
    mut v_found_162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_163_ = l_Lean_Expr_FindStep_found_elim___redArg(v_found_162_);
    leanh::lean_dec(v_found_162_);
    return v_res_163_;
}
pub unsafe fn l_Lean_Expr_FindStep_found_elim(
    mut v_motive_164_: *mut leanh::LeanObject,
    mut v_t_165_: u8,
    mut v_h_166_: *mut leanh::LeanObject,
    mut v_found_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_found_167_);
    return v_found_167_;
}
pub unsafe fn l_Lean_Expr_FindStep_found_elim___boxed(
    mut v_motive_168_: *mut leanh::LeanObject,
    mut v_t_169_: *mut leanh::LeanObject,
    mut v_h_170_: *mut leanh::LeanObject,
    mut v_found_171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_172_: u8 = 0;
    let mut v_res_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_172_ = (leanh::lean_unbox(v_t_169_) as u8);
    v_res_173_ =
        l_Lean_Expr_FindStep_found_elim(v_motive_168_, v_t_boxed_172_, v_h_170_, v_found_171_);
    leanh::lean_dec(v_found_171_);
    return v_res_173_;
}
pub unsafe fn l_Lean_Expr_FindStep_visit_elim___redArg(
    mut v_visit_174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_visit_174_);
    return v_visit_174_;
}
pub unsafe fn l_Lean_Expr_FindStep_visit_elim___redArg___boxed(
    mut v_visit_175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_176_ = l_Lean_Expr_FindStep_visit_elim___redArg(v_visit_175_);
    leanh::lean_dec(v_visit_175_);
    return v_res_176_;
}
pub unsafe fn l_Lean_Expr_FindStep_visit_elim(
    mut v_motive_177_: *mut leanh::LeanObject,
    mut v_t_178_: u8,
    mut v_h_179_: *mut leanh::LeanObject,
    mut v_visit_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_visit_180_);
    return v_visit_180_;
}
pub unsafe fn l_Lean_Expr_FindStep_visit_elim___boxed(
    mut v_motive_181_: *mut leanh::LeanObject,
    mut v_t_182_: *mut leanh::LeanObject,
    mut v_h_183_: *mut leanh::LeanObject,
    mut v_visit_184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_185_: u8 = 0;
    let mut v_res_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_185_ = (leanh::lean_unbox(v_t_182_) as u8);
    v_res_186_ =
        l_Lean_Expr_FindStep_visit_elim(v_motive_181_, v_t_boxed_185_, v_h_183_, v_visit_184_);
    leanh::lean_dec(v_visit_184_);
    return v_res_186_;
}
pub unsafe fn l_Lean_Expr_FindStep_done_elim___redArg(
    mut v_done_187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_done_187_);
    return v_done_187_;
}
pub unsafe fn l_Lean_Expr_FindStep_done_elim___redArg___boxed(
    mut v_done_188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_189_ = l_Lean_Expr_FindStep_done_elim___redArg(v_done_188_);
    leanh::lean_dec(v_done_188_);
    return v_res_189_;
}
pub unsafe fn l_Lean_Expr_FindStep_done_elim(
    mut v_motive_190_: *mut leanh::LeanObject,
    mut v_t_191_: u8,
    mut v_h_192_: *mut leanh::LeanObject,
    mut v_done_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_done_193_);
    return v_done_193_;
}
pub unsafe fn l_Lean_Expr_FindStep_done_elim___boxed(
    mut v_motive_194_: *mut leanh::LeanObject,
    mut v_t_195_: *mut leanh::LeanObject,
    mut v_h_196_: *mut leanh::LeanObject,
    mut v_done_197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_198_: u8 = 0;
    let mut v_res_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_198_ = (leanh::lean_unbox(v_t_195_) as u8);
    v_res_199_ =
        l_Lean_Expr_FindStep_done_elim(v_motive_194_, v_t_boxed_198_, v_h_196_, v_done_197_);
    leanh::lean_dec(v_done_197_);
    return v_res_199_;
}
pub unsafe fn l_Lean_Expr_findExtImpl_x3f___boxed(
    mut v_p_202_: *mut leanh::LeanObject,
    mut v_e_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_204_ = lean_find_ext_expr(v_p_202_, v_e_203_);
    leanh::lean_dec_ref(v_e_203_);
    leanh::lean_dec_ref(v_p_202_);
    return v_res_204_;
}
pub unsafe fn l_Lean_Expr_findExt_x3f(
    mut v_p_205_: *mut leanh::LeanObject,
    mut v_e_206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_207_ = lean_find_ext_expr(v_p_205_, v_e_206_);
    return v___x_207_;
}
pub unsafe fn l_Lean_Expr_findExt_x3f___boxed(
    mut v_p_208_: *mut leanh::LeanObject,
    mut v_e_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_210_ = l_Lean_Expr_findExt_x3f(v_p_208_, v_e_209_);
    leanh::lean_dec_ref(v_e_209_);
    leanh::lean_dec_ref(v_p_208_);
    return v_res_210_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_FindExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_FindExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_FindExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FindExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_FindExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_FindExpr(builtin);
}
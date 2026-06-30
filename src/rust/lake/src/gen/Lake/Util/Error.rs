// Lean compiler output
// Module: Lake.Util.Error
// Imports: Init.System.IO
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_EIO_toBaseIO___boxed, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
pub static l_Lake_instMonadErrorIO___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadErrorIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadErrorIO___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorIO___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instMonadErrorIO: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorIO___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadErrorEIOString___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadErrorEIOString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadErrorEIOString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorEIOString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instMonadErrorEIOString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorEIOString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instMonadErrorExceptString___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadErrorExceptString___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadErrorExceptString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorExceptString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instMonadErrorExceptString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorExceptString___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(
    mut v_inst_109_: *mut leanh::LeanObject,
    mut v_inst_110_: *mut leanh::LeanObject,
    mut v_00_u03b1_111_: *mut leanh::LeanObject,
    mut v_msg_112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_113_ = leanh::lean_apply_2(v_inst_109_, leanh::lean_box(0), v_msg_112_);
    v___x_114_ = leanh::lean_apply_2(v_inst_110_, leanh::lean_box(0), v___x_113_);
    return v___x_114_;
}
pub unsafe fn l_Lake_instMonadErrorOfMonadLift___redArg(
    mut v_inst_115_: *mut leanh::LeanObject,
    mut v_inst_116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_117_ = leanh::lean_alloc_closure(
        l_Lake_instMonadErrorOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_117_, 0, v_inst_116_);
    leanh::lean_closure_set(v___f_117_, 1, v_inst_115_);
    return v___f_117_;
}
pub unsafe fn l_Lake_instMonadErrorOfMonadLift(
    mut v_m_118_: *mut leanh::LeanObject,
    mut v_n_119_: *mut leanh::LeanObject,
    mut v_inst_120_: *mut leanh::LeanObject,
    mut v_inst_121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_122_ = leanh::lean_alloc_closure(
        l_Lake_instMonadErrorOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_122_, 0, v_inst_121_);
    leanh::lean_closure_set(v___f_122_, 1, v_inst_120_);
    return v___f_122_;
}
pub unsafe fn l_Lake_instMonadErrorIO___lam__0(
    mut v_00_u03b1_123_: *mut leanh::LeanObject,
    mut v_msg_124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_126_ = lean_mk_io_user_error(v_msg_124_);
    v___x_127_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_127_, 0, v___x_126_);
    return v___x_127_;
}
pub unsafe fn l_Lake_instMonadErrorIO___lam__0___boxed(
    mut v_00_u03b1_128_: *mut leanh::LeanObject,
    mut v_msg_129_: *mut leanh::LeanObject,
    mut v___y_130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_131_ = l_Lake_instMonadErrorIO___lam__0(v_00_u03b1_128_, v_msg_129_);
    return v_res_131_;
}
pub unsafe fn l_Lake_instMonadErrorEIOString___lam__0(
    mut v_00_u03b1_134_: *mut leanh::LeanObject,
    mut v_msg_135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_137_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_137_, 0, v_msg_135_);
    return v___x_137_;
}
pub unsafe fn l_Lake_instMonadErrorEIOString___lam__0___boxed(
    mut v_00_u03b1_138_: *mut leanh::LeanObject,
    mut v_msg_139_: *mut leanh::LeanObject,
    mut v___y_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_141_ = l_Lake_instMonadErrorEIOString___lam__0(v_00_u03b1_138_, v_msg_139_);
    return v_res_141_;
}
pub unsafe fn l_Lake_instMonadErrorExceptString___lam__0(
    mut v_00_u03b1_144_: *mut leanh::LeanObject,
    mut v_msg_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_146_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_146_, 0, v_msg_145_);
    return v___x_146_;
}
pub unsafe fn l_Lake_MonadError_runEIO___redArg___lam__0(
    mut v_inst_149_: *mut leanh::LeanObject,
    mut v_inst_150_: *mut leanh::LeanObject,
    mut v_toPure_151_: *mut leanh::LeanObject,
    mut v_____do__lift_152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_152_) == 0 {
        let mut v_a_153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_151_);
        v_a_153_ = leanh::lean_ctor_get(v_____do__lift_152_, 0);
        leanh::lean_inc(v_a_153_);
        leanh::lean_dec_ref_known(v_____do__lift_152_, 1);
        v___x_154_ = leanh::lean_apply_1(v_inst_149_, v_a_153_);
        v___x_155_ = leanh::lean_apply_2(v_inst_150_, leanh::lean_box(0), v___x_154_);
        return v___x_155_;
    } else {
        let mut v_a_156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_150_);
        leanh::lean_dec_ref(v_inst_149_);
        v_a_156_ = leanh::lean_ctor_get(v_____do__lift_152_, 0);
        leanh::lean_inc(v_a_156_);
        leanh::lean_dec_ref_known(v_____do__lift_152_, 1);
        v___x_157_ = leanh::lean_apply_2(v_toPure_151_, leanh::lean_box(0), v_a_156_);
        return v___x_157_;
    }
}
pub unsafe fn l_Lake_MonadError_runEIO___redArg(
    mut v_inst_158_: *mut leanh::LeanObject,
    mut v_inst_159_: *mut leanh::LeanObject,
    mut v_inst_160_: *mut leanh::LeanObject,
    mut v_inst_161_: *mut leanh::LeanObject,
    mut v_x_162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_163_ = leanh::lean_ctor_get(v_inst_158_, 0);
    leanh::lean_inc_ref(v_toApplicative_163_);
    v_toBind_164_ = leanh::lean_ctor_get(v_inst_158_, 1);
    leanh::lean_inc(v_toBind_164_);
    leanh::lean_dec_ref(v_inst_158_);
    v_toPure_165_ = leanh::lean_ctor_get(v_toApplicative_163_, 1);
    leanh::lean_inc(v_toPure_165_);
    leanh::lean_dec_ref(v_toApplicative_163_);
    v___x_166_ =
        leanh::lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_166_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_166_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_166_, 2, v_x_162_);
    v___x_167_ = leanh::lean_apply_2(v_inst_160_, leanh::lean_box(0), v___x_166_);
    v___f_168_ = leanh::lean_alloc_closure(
        l_Lake_MonadError_runEIO___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_168_, 0, v_inst_161_);
    leanh::lean_closure_set(v___f_168_, 1, v_inst_159_);
    leanh::lean_closure_set(v___f_168_, 2, v_toPure_165_);
    v___x_169_ = leanh::lean_apply_4(
        v_toBind_164_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_167_,
        v___f_168_,
    );
    return v___x_169_;
}
pub unsafe fn l_Lake_MonadError_runEIO(
    mut v_m_170_: *mut leanh::LeanObject,
    mut v_00_u03b5_171_: *mut leanh::LeanObject,
    mut v_00_u03b1_172_: *mut leanh::LeanObject,
    mut v_inst_173_: *mut leanh::LeanObject,
    mut v_inst_174_: *mut leanh::LeanObject,
    mut v_inst_175_: *mut leanh::LeanObject,
    mut v_inst_176_: *mut leanh::LeanObject,
    mut v_x_177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_178_ = leanh::lean_ctor_get(v_inst_173_, 0);
    leanh::lean_inc_ref(v_toApplicative_178_);
    v_toBind_179_ = leanh::lean_ctor_get(v_inst_173_, 1);
    leanh::lean_inc(v_toBind_179_);
    leanh::lean_dec_ref(v_inst_173_);
    v_toPure_180_ = leanh::lean_ctor_get(v_toApplicative_178_, 1);
    leanh::lean_inc(v_toPure_180_);
    leanh::lean_dec_ref(v_toApplicative_178_);
    v___x_181_ =
        leanh::lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_181_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_181_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_181_, 2, v_x_177_);
    v___x_182_ = leanh::lean_apply_2(v_inst_175_, leanh::lean_box(0), v___x_181_);
    v___f_183_ = leanh::lean_alloc_closure(
        l_Lake_MonadError_runEIO___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_183_, 0, v_inst_176_);
    leanh::lean_closure_set(v___f_183_, 1, v_inst_174_);
    leanh::lean_closure_set(v___f_183_, 2, v_toPure_180_);
    v___x_184_ = leanh::lean_apply_4(
        v_toBind_179_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_182_,
        v___f_183_,
    );
    return v___x_184_;
}
pub unsafe fn l_Lake_MonadError_runIO___redArg___lam__0(
    mut v_inst_185_: *mut leanh::LeanObject,
    mut v_toPure_186_: *mut leanh::LeanObject,
    mut v_____do__lift_187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_187_) == 0 {
        let mut v_a_188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_186_);
        v_a_188_ = leanh::lean_ctor_get(v_____do__lift_187_, 0);
        leanh::lean_inc(v_a_188_);
        leanh::lean_dec_ref_known(v_____do__lift_187_, 1);
        v___x_189_ = lean_io_error_to_string(v_a_188_);
        v___x_190_ = leanh::lean_apply_2(v_inst_185_, leanh::lean_box(0), v___x_189_);
        return v___x_190_;
    } else {
        let mut v_a_191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_185_);
        v_a_191_ = leanh::lean_ctor_get(v_____do__lift_187_, 0);
        leanh::lean_inc(v_a_191_);
        leanh::lean_dec_ref_known(v_____do__lift_187_, 1);
        v___x_192_ = leanh::lean_apply_2(v_toPure_186_, leanh::lean_box(0), v_a_191_);
        return v___x_192_;
    }
}
pub unsafe fn l_Lake_MonadError_runIO___redArg(
    mut v_inst_193_: *mut leanh::LeanObject,
    mut v_inst_194_: *mut leanh::LeanObject,
    mut v_inst_195_: *mut leanh::LeanObject,
    mut v_x_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_197_ = leanh::lean_ctor_get(v_inst_193_, 0);
    leanh::lean_inc_ref(v_toApplicative_197_);
    v_toBind_198_ = leanh::lean_ctor_get(v_inst_193_, 1);
    leanh::lean_inc(v_toBind_198_);
    leanh::lean_dec_ref(v_inst_193_);
    v_toPure_199_ = leanh::lean_ctor_get(v_toApplicative_197_, 1);
    leanh::lean_inc(v_toPure_199_);
    leanh::lean_dec_ref(v_toApplicative_197_);
    v___x_200_ =
        leanh::lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_200_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_200_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_200_, 2, v_x_196_);
    v___x_201_ = leanh::lean_apply_2(v_inst_195_, leanh::lean_box(0), v___x_200_);
    v___f_202_ = leanh::lean_alloc_closure(
        l_Lake_MonadError_runIO___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_202_, 0, v_inst_194_);
    leanh::lean_closure_set(v___f_202_, 1, v_toPure_199_);
    v___x_203_ = leanh::lean_apply_4(
        v_toBind_198_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_201_,
        v___f_202_,
    );
    return v___x_203_;
}
pub unsafe fn l_Lake_MonadError_runIO(
    mut v_m_204_: *mut leanh::LeanObject,
    mut v_00_u03b1_205_: *mut leanh::LeanObject,
    mut v_inst_206_: *mut leanh::LeanObject,
    mut v_inst_207_: *mut leanh::LeanObject,
    mut v_inst_208_: *mut leanh::LeanObject,
    mut v_x_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_210_ = leanh::lean_ctor_get(v_inst_206_, 0);
    leanh::lean_inc_ref(v_toApplicative_210_);
    v_toBind_211_ = leanh::lean_ctor_get(v_inst_206_, 1);
    leanh::lean_inc(v_toBind_211_);
    leanh::lean_dec_ref(v_inst_206_);
    v_toPure_212_ = leanh::lean_ctor_get(v_toApplicative_210_, 1);
    leanh::lean_inc(v_toPure_212_);
    leanh::lean_dec_ref(v_toApplicative_210_);
    v___x_213_ =
        leanh::lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_213_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_213_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_213_, 2, v_x_209_);
    v___x_214_ = leanh::lean_apply_2(v_inst_208_, leanh::lean_box(0), v___x_213_);
    v___f_215_ = leanh::lean_alloc_closure(
        l_Lake_MonadError_runIO___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_215_, 0, v_inst_207_);
    leanh::lean_closure_set(v___f_215_, 1, v_toPure_212_);
    v___x_216_ = leanh::lean_apply_4(
        v_toBind_211_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_214_,
        v___f_215_,
    );
    return v___x_216_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Error(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Error(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Error(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Error(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Error(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Error(builtin);
}
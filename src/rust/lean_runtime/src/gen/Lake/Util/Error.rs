// Lean compiler output
// Module: Lake.Util.Error
// Imports: Init.System.IO
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_EIO_toBaseIO___boxed, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
pub static l_Lake_instMonadErrorIO___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadErrorIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadErrorIO___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorIO___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadErrorIO: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorIO___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadErrorEIOString___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadErrorEIOString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadErrorEIOString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorEIOString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadErrorEIOString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorEIOString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadErrorExceptString___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadErrorExceptString___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadErrorExceptString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorExceptString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadErrorExceptString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorExceptString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(
    mut v_inst_109_: *mut crate::leanh::LeanObject,
    mut v_inst_110_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_111_: *mut crate::leanh::LeanObject,
    mut v_msg_112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_113_ = crate::leanh::lean_apply_2(v_inst_109_, crate::leanh::lean_box(0), v_msg_112_);
    v___x_114_ = crate::leanh::lean_apply_2(v_inst_110_, crate::leanh::lean_box(0), v___x_113_);
    return v___x_114_;
}
pub unsafe fn l_Lake_instMonadErrorOfMonadLift___redArg(
    mut v_inst_115_: *mut crate::leanh::LeanObject,
    mut v_inst_116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_117_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadErrorOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_117_, 0, v_inst_116_);
    crate::leanh::lean_closure_set(v___f_117_, 1, v_inst_115_);
    return v___f_117_;
}
pub unsafe fn l_Lake_instMonadErrorOfMonadLift(
    mut v_m_118_: *mut crate::leanh::LeanObject,
    mut v_n_119_: *mut crate::leanh::LeanObject,
    mut v_inst_120_: *mut crate::leanh::LeanObject,
    mut v_inst_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_122_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadErrorOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_122_, 0, v_inst_121_);
    crate::leanh::lean_closure_set(v___f_122_, 1, v_inst_120_);
    return v___f_122_;
}
pub unsafe fn l_Lake_instMonadErrorIO___lam__0(
    mut v_00_u03b1_123_: *mut crate::leanh::LeanObject,
    mut v_msg_124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_126_ = lean_mk_io_user_error(v_msg_124_);
    v___x_127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_127_, 0, v___x_126_);
    return v___x_127_;
}
pub unsafe fn l_Lake_instMonadErrorIO___lam__0___boxed(
    mut v_00_u03b1_128_: *mut crate::leanh::LeanObject,
    mut v_msg_129_: *mut crate::leanh::LeanObject,
    mut v___y_130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_131_ = l_Lake_instMonadErrorIO___lam__0(v_00_u03b1_128_, v_msg_129_);
    return v_res_131_;
}
pub unsafe fn l_Lake_instMonadErrorEIOString___lam__0(
    mut v_00_u03b1_134_: *mut crate::leanh::LeanObject,
    mut v_msg_135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_137_, 0, v_msg_135_);
    return v___x_137_;
}
pub unsafe fn l_Lake_instMonadErrorEIOString___lam__0___boxed(
    mut v_00_u03b1_138_: *mut crate::leanh::LeanObject,
    mut v_msg_139_: *mut crate::leanh::LeanObject,
    mut v___y_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_141_ = l_Lake_instMonadErrorEIOString___lam__0(v_00_u03b1_138_, v_msg_139_);
    return v_res_141_;
}
pub unsafe fn l_Lake_instMonadErrorExceptString___lam__0(
    mut v_00_u03b1_144_: *mut crate::leanh::LeanObject,
    mut v_msg_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_146_, 0, v_msg_145_);
    return v___x_146_;
}
pub unsafe fn l_Lake_MonadError_runEIO___redArg___lam__0(
    mut v_inst_149_: *mut crate::leanh::LeanObject,
    mut v_inst_150_: *mut crate::leanh::LeanObject,
    mut v_toPure_151_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_152_) == 0 {
        let mut v_a_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_151_);
        v_a_153_ = crate::leanh::lean_ctor_get(v_____do__lift_152_, 0);
        crate::leanh::lean_inc(v_a_153_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_152_, 1);
        v___x_154_ = crate::leanh::lean_apply_1(v_inst_149_, v_a_153_);
        v___x_155_ = crate::leanh::lean_apply_2(v_inst_150_, crate::leanh::lean_box(0), v___x_154_);
        return v___x_155_;
    } else {
        let mut v_a_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_150_);
        crate::leanh::lean_dec_ref(v_inst_149_);
        v_a_156_ = crate::leanh::lean_ctor_get(v_____do__lift_152_, 0);
        crate::leanh::lean_inc(v_a_156_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_152_, 1);
        v___x_157_ = crate::leanh::lean_apply_2(v_toPure_151_, crate::leanh::lean_box(0), v_a_156_);
        return v___x_157_;
    }
}
pub unsafe fn l_Lake_MonadError_runEIO___redArg(
    mut v_inst_158_: *mut crate::leanh::LeanObject,
    mut v_inst_159_: *mut crate::leanh::LeanObject,
    mut v_inst_160_: *mut crate::leanh::LeanObject,
    mut v_inst_161_: *mut crate::leanh::LeanObject,
    mut v_x_162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_163_ = crate::leanh::lean_ctor_get(v_inst_158_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_163_);
    v_toBind_164_ = crate::leanh::lean_ctor_get(v_inst_158_, 1);
    crate::leanh::lean_inc(v_toBind_164_);
    crate::leanh::lean_dec_ref(v_inst_158_);
    v_toPure_165_ = crate::leanh::lean_ctor_get(v_toApplicative_163_, 1);
    crate::leanh::lean_inc(v_toPure_165_);
    crate::leanh::lean_dec_ref(v_toApplicative_163_);
    v___x_166_ =
        crate::leanh::lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_166_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_166_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_166_, 2, v_x_162_);
    v___x_167_ = crate::leanh::lean_apply_2(v_inst_160_, crate::leanh::lean_box(0), v___x_166_);
    v___f_168_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadError_runEIO___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_168_, 0, v_inst_161_);
    crate::leanh::lean_closure_set(v___f_168_, 1, v_inst_159_);
    crate::leanh::lean_closure_set(v___f_168_, 2, v_toPure_165_);
    v___x_169_ = crate::leanh::lean_apply_4(
        v_toBind_164_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_167_,
        v___f_168_,
    );
    return v___x_169_;
}
pub unsafe fn l_Lake_MonadError_runEIO(
    mut v_m_170_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_171_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_172_: *mut crate::leanh::LeanObject,
    mut v_inst_173_: *mut crate::leanh::LeanObject,
    mut v_inst_174_: *mut crate::leanh::LeanObject,
    mut v_inst_175_: *mut crate::leanh::LeanObject,
    mut v_inst_176_: *mut crate::leanh::LeanObject,
    mut v_x_177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_178_ = crate::leanh::lean_ctor_get(v_inst_173_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_178_);
    v_toBind_179_ = crate::leanh::lean_ctor_get(v_inst_173_, 1);
    crate::leanh::lean_inc(v_toBind_179_);
    crate::leanh::lean_dec_ref(v_inst_173_);
    v_toPure_180_ = crate::leanh::lean_ctor_get(v_toApplicative_178_, 1);
    crate::leanh::lean_inc(v_toPure_180_);
    crate::leanh::lean_dec_ref(v_toApplicative_178_);
    v___x_181_ =
        crate::leanh::lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_181_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_181_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_181_, 2, v_x_177_);
    v___x_182_ = crate::leanh::lean_apply_2(v_inst_175_, crate::leanh::lean_box(0), v___x_181_);
    v___f_183_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadError_runEIO___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_183_, 0, v_inst_176_);
    crate::leanh::lean_closure_set(v___f_183_, 1, v_inst_174_);
    crate::leanh::lean_closure_set(v___f_183_, 2, v_toPure_180_);
    v___x_184_ = crate::leanh::lean_apply_4(
        v_toBind_179_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_182_,
        v___f_183_,
    );
    return v___x_184_;
}
pub unsafe fn l_Lake_MonadError_runIO___redArg___lam__0(
    mut v_inst_185_: *mut crate::leanh::LeanObject,
    mut v_toPure_186_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_187_) == 0 {
        let mut v_a_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_186_);
        v_a_188_ = crate::leanh::lean_ctor_get(v_____do__lift_187_, 0);
        crate::leanh::lean_inc(v_a_188_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_187_, 1);
        v___x_189_ = lean_io_error_to_string(v_a_188_);
        v___x_190_ = crate::leanh::lean_apply_2(v_inst_185_, crate::leanh::lean_box(0), v___x_189_);
        return v___x_190_;
    } else {
        let mut v_a_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_185_);
        v_a_191_ = crate::leanh::lean_ctor_get(v_____do__lift_187_, 0);
        crate::leanh::lean_inc(v_a_191_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_187_, 1);
        v___x_192_ = crate::leanh::lean_apply_2(v_toPure_186_, crate::leanh::lean_box(0), v_a_191_);
        return v___x_192_;
    }
}
pub unsafe fn l_Lake_MonadError_runIO___redArg(
    mut v_inst_193_: *mut crate::leanh::LeanObject,
    mut v_inst_194_: *mut crate::leanh::LeanObject,
    mut v_inst_195_: *mut crate::leanh::LeanObject,
    mut v_x_196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_197_ = crate::leanh::lean_ctor_get(v_inst_193_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_197_);
    v_toBind_198_ = crate::leanh::lean_ctor_get(v_inst_193_, 1);
    crate::leanh::lean_inc(v_toBind_198_);
    crate::leanh::lean_dec_ref(v_inst_193_);
    v_toPure_199_ = crate::leanh::lean_ctor_get(v_toApplicative_197_, 1);
    crate::leanh::lean_inc(v_toPure_199_);
    crate::leanh::lean_dec_ref(v_toApplicative_197_);
    v___x_200_ =
        crate::leanh::lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_200_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_200_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_200_, 2, v_x_196_);
    v___x_201_ = crate::leanh::lean_apply_2(v_inst_195_, crate::leanh::lean_box(0), v___x_200_);
    v___f_202_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadError_runIO___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_202_, 0, v_inst_194_);
    crate::leanh::lean_closure_set(v___f_202_, 1, v_toPure_199_);
    v___x_203_ = crate::leanh::lean_apply_4(
        v_toBind_198_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_201_,
        v___f_202_,
    );
    return v___x_203_;
}
pub unsafe fn l_Lake_MonadError_runIO(
    mut v_m_204_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_205_: *mut crate::leanh::LeanObject,
    mut v_inst_206_: *mut crate::leanh::LeanObject,
    mut v_inst_207_: *mut crate::leanh::LeanObject,
    mut v_inst_208_: *mut crate::leanh::LeanObject,
    mut v_x_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_210_ = crate::leanh::lean_ctor_get(v_inst_206_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_210_);
    v_toBind_211_ = crate::leanh::lean_ctor_get(v_inst_206_, 1);
    crate::leanh::lean_inc(v_toBind_211_);
    crate::leanh::lean_dec_ref(v_inst_206_);
    v_toPure_212_ = crate::leanh::lean_ctor_get(v_toApplicative_210_, 1);
    crate::leanh::lean_inc(v_toPure_212_);
    crate::leanh::lean_dec_ref(v_toApplicative_210_);
    v___x_213_ =
        crate::leanh::lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_213_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_213_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_213_, 2, v_x_209_);
    v___x_214_ = crate::leanh::lean_apply_2(v_inst_208_, crate::leanh::lean_box(0), v___x_213_);
    v___f_215_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadError_runIO___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_215_, 0, v_inst_207_);
    crate::leanh::lean_closure_set(v___f_215_, 1, v_toPure_212_);
    v___x_216_ = crate::leanh::lean_apply_4(
        v_toBind_211_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_214_,
        v___f_215_,
    );
    return v___x_216_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Error(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Error(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Error(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Error(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Error(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Error(builtin);
}

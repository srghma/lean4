// Lean compiler output
// Module: Lake.Util.Error
// Imports: Init.System.IO
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_EIO_toBaseIO___boxed, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub static l_Lake_instMonadErrorIO___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMonadErrorIO___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadErrorIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorIO___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMonadErrorIO: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorIO___closed__0_value) as *mut LeanObject;
pub static l_Lake_instMonadErrorEIOString___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadErrorEIOString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadErrorEIOString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorEIOString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMonadErrorEIOString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorEIOString___closed__0_value) as *mut LeanObject;
pub static l_Lake_instMonadErrorExceptString___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadErrorExceptString___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadErrorExceptString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorExceptString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMonadErrorExceptString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorExceptString___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(
    mut v_inst_109_: *mut LeanObject,
    mut v_inst_110_: *mut LeanObject,
    mut v_00_u03b1_111_: *mut LeanObject,
    mut v_msg_112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    v___x_113_ = lean_apply_2(v_inst_109_, lean_box(0), v_msg_112_);
    v___x_114_ = lean_apply_2(v_inst_110_, lean_box(0), v___x_113_);
    return v___x_114_;
}
pub unsafe fn l_Lake_instMonadErrorOfMonadLift___redArg(
    mut v_inst_115_: *mut LeanObject,
    mut v_inst_116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_117_: *mut LeanObject = core::ptr::null_mut();
    v___f_117_ = lean_alloc_closure(
        l_Lake_instMonadErrorOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_117_, 0, v_inst_116_);
    lean_closure_set(v___f_117_, 1, v_inst_115_);
    return v___f_117_;
}
pub unsafe fn l_Lake_instMonadErrorOfMonadLift(
    mut v_m_118_: *mut LeanObject,
    mut v_n_119_: *mut LeanObject,
    mut v_inst_120_: *mut LeanObject,
    mut v_inst_121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_122_: *mut LeanObject = core::ptr::null_mut();
    v___f_122_ = lean_alloc_closure(
        l_Lake_instMonadErrorOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_122_, 0, v_inst_121_);
    lean_closure_set(v___f_122_, 1, v_inst_120_);
    return v___f_122_;
}
pub unsafe fn l_Lake_instMonadErrorIO___lam__0(
    mut v_00_u03b1_123_: *mut LeanObject,
    mut v_msg_124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
    v___x_126_ = lean_mk_io_user_error(v_msg_124_);
    v___x_127_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_127_, 0, v___x_126_);
    return v___x_127_;
}
pub unsafe fn l_Lake_instMonadErrorIO___lam__0___boxed(
    mut v_00_u03b1_128_: *mut LeanObject,
    mut v_msg_129_: *mut LeanObject,
    mut v___y_130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_131_: *mut LeanObject = core::ptr::null_mut();
    v_res_131_ = l_Lake_instMonadErrorIO___lam__0(v_00_u03b1_128_, v_msg_129_);
    return v_res_131_;
}
pub unsafe fn l_Lake_instMonadErrorEIOString___lam__0(
    mut v_00_u03b1_134_: *mut LeanObject,
    mut v_msg_135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    v___x_137_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_137_, 0, v_msg_135_);
    return v___x_137_;
}
pub unsafe fn l_Lake_instMonadErrorEIOString___lam__0___boxed(
    mut v_00_u03b1_138_: *mut LeanObject,
    mut v_msg_139_: *mut LeanObject,
    mut v___y_140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_141_: *mut LeanObject = core::ptr::null_mut();
    v_res_141_ = l_Lake_instMonadErrorEIOString___lam__0(v_00_u03b1_138_, v_msg_139_);
    return v_res_141_;
}
pub unsafe fn l_Lake_instMonadErrorExceptString___lam__0(
    mut v_00_u03b1_144_: *mut LeanObject,
    mut v_msg_145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    v___x_146_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_146_, 0, v_msg_145_);
    return v___x_146_;
}
pub unsafe fn l_Lake_MonadError_runEIO___redArg___lam__0(
    mut v_inst_149_: *mut LeanObject,
    mut v_inst_150_: *mut LeanObject,
    mut v_toPure_151_: *mut LeanObject,
    mut v_____do__lift_152_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_152_) == 0 {
        let mut v_a_153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_151_);
        v_a_153_ = lean_ctor_get(v_____do__lift_152_, 0);
        lean_inc(v_a_153_);
        lean_dec_ref_known(v_____do__lift_152_, 1);
        v___x_154_ = lean_apply_1(v_inst_149_, v_a_153_);
        v___x_155_ = lean_apply_2(v_inst_150_, lean_box(0), v___x_154_);
        return v___x_155_;
    } else {
        let mut v_a_156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_150_);
        lean_dec_ref(v_inst_149_);
        v_a_156_ = lean_ctor_get(v_____do__lift_152_, 0);
        lean_inc(v_a_156_);
        lean_dec_ref_known(v_____do__lift_152_, 1);
        v___x_157_ = lean_apply_2(v_toPure_151_, lean_box(0), v_a_156_);
        return v___x_157_;
    }
}
pub unsafe fn l_Lake_MonadError_runEIO___redArg(
    mut v_inst_158_: *mut LeanObject,
    mut v_inst_159_: *mut LeanObject,
    mut v_inst_160_: *mut LeanObject,
    mut v_inst_161_: *mut LeanObject,
    mut v_x_162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_163_ = lean_ctor_get(v_inst_158_, 0);
    lean_inc_ref(v_toApplicative_163_);
    v_toBind_164_ = lean_ctor_get(v_inst_158_, 1);
    lean_inc(v_toBind_164_);
    lean_dec_ref(v_inst_158_);
    v_toPure_165_ = lean_ctor_get(v_toApplicative_163_, 1);
    lean_inc(v_toPure_165_);
    lean_dec_ref(v_toApplicative_163_);
    v___x_166_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_166_, 0, lean_box(0));
    lean_closure_set(v___x_166_, 1, lean_box(0));
    lean_closure_set(v___x_166_, 2, v_x_162_);
    v___x_167_ = lean_apply_2(v_inst_160_, lean_box(0), v___x_166_);
    v___f_168_ = lean_alloc_closure(
        l_Lake_MonadError_runEIO___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_168_, 0, v_inst_161_);
    lean_closure_set(v___f_168_, 1, v_inst_159_);
    lean_closure_set(v___f_168_, 2, v_toPure_165_);
    v___x_169_ = lean_apply_4(
        v_toBind_164_,
        lean_box(0),
        lean_box(0),
        v___x_167_,
        v___f_168_,
    );
    return v___x_169_;
}
pub unsafe fn l_Lake_MonadError_runEIO(
    mut v_m_170_: *mut LeanObject,
    mut v_00_u03b5_171_: *mut LeanObject,
    mut v_00_u03b1_172_: *mut LeanObject,
    mut v_inst_173_: *mut LeanObject,
    mut v_inst_174_: *mut LeanObject,
    mut v_inst_175_: *mut LeanObject,
    mut v_inst_176_: *mut LeanObject,
    mut v_x_177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_178_ = lean_ctor_get(v_inst_173_, 0);
    lean_inc_ref(v_toApplicative_178_);
    v_toBind_179_ = lean_ctor_get(v_inst_173_, 1);
    lean_inc(v_toBind_179_);
    lean_dec_ref(v_inst_173_);
    v_toPure_180_ = lean_ctor_get(v_toApplicative_178_, 1);
    lean_inc(v_toPure_180_);
    lean_dec_ref(v_toApplicative_178_);
    v___x_181_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_181_, 0, lean_box(0));
    lean_closure_set(v___x_181_, 1, lean_box(0));
    lean_closure_set(v___x_181_, 2, v_x_177_);
    v___x_182_ = lean_apply_2(v_inst_175_, lean_box(0), v___x_181_);
    v___f_183_ = lean_alloc_closure(
        l_Lake_MonadError_runEIO___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_183_, 0, v_inst_176_);
    lean_closure_set(v___f_183_, 1, v_inst_174_);
    lean_closure_set(v___f_183_, 2, v_toPure_180_);
    v___x_184_ = lean_apply_4(
        v_toBind_179_,
        lean_box(0),
        lean_box(0),
        v___x_182_,
        v___f_183_,
    );
    return v___x_184_;
}
pub unsafe fn l_Lake_MonadError_runIO___redArg___lam__0(
    mut v_inst_185_: *mut LeanObject,
    mut v_toPure_186_: *mut LeanObject,
    mut v_____do__lift_187_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_187_) == 0 {
        let mut v_a_188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_186_);
        v_a_188_ = lean_ctor_get(v_____do__lift_187_, 0);
        lean_inc(v_a_188_);
        lean_dec_ref_known(v_____do__lift_187_, 1);
        v___x_189_ = lean_io_error_to_string(v_a_188_);
        v___x_190_ = lean_apply_2(v_inst_185_, lean_box(0), v___x_189_);
        return v___x_190_;
    } else {
        let mut v_a_191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_185_);
        v_a_191_ = lean_ctor_get(v_____do__lift_187_, 0);
        lean_inc(v_a_191_);
        lean_dec_ref_known(v_____do__lift_187_, 1);
        v___x_192_ = lean_apply_2(v_toPure_186_, lean_box(0), v_a_191_);
        return v___x_192_;
    }
}
pub unsafe fn l_Lake_MonadError_runIO___redArg(
    mut v_inst_193_: *mut LeanObject,
    mut v_inst_194_: *mut LeanObject,
    mut v_inst_195_: *mut LeanObject,
    mut v_x_196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_197_ = lean_ctor_get(v_inst_193_, 0);
    lean_inc_ref(v_toApplicative_197_);
    v_toBind_198_ = lean_ctor_get(v_inst_193_, 1);
    lean_inc(v_toBind_198_);
    lean_dec_ref(v_inst_193_);
    v_toPure_199_ = lean_ctor_get(v_toApplicative_197_, 1);
    lean_inc(v_toPure_199_);
    lean_dec_ref(v_toApplicative_197_);
    v___x_200_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_200_, 0, lean_box(0));
    lean_closure_set(v___x_200_, 1, lean_box(0));
    lean_closure_set(v___x_200_, 2, v_x_196_);
    v___x_201_ = lean_apply_2(v_inst_195_, lean_box(0), v___x_200_);
    v___f_202_ = lean_alloc_closure(
        l_Lake_MonadError_runIO___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_202_, 0, v_inst_194_);
    lean_closure_set(v___f_202_, 1, v_toPure_199_);
    v___x_203_ = lean_apply_4(
        v_toBind_198_,
        lean_box(0),
        lean_box(0),
        v___x_201_,
        v___f_202_,
    );
    return v___x_203_;
}
pub unsafe fn l_Lake_MonadError_runIO(
    mut v_m_204_: *mut LeanObject,
    mut v_00_u03b1_205_: *mut LeanObject,
    mut v_inst_206_: *mut LeanObject,
    mut v_inst_207_: *mut LeanObject,
    mut v_inst_208_: *mut LeanObject,
    mut v_x_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_210_ = lean_ctor_get(v_inst_206_, 0);
    lean_inc_ref(v_toApplicative_210_);
    v_toBind_211_ = lean_ctor_get(v_inst_206_, 1);
    lean_inc(v_toBind_211_);
    lean_dec_ref(v_inst_206_);
    v_toPure_212_ = lean_ctor_get(v_toApplicative_210_, 1);
    lean_inc(v_toPure_212_);
    lean_dec_ref(v_toApplicative_210_);
    v___x_213_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_213_, 0, lean_box(0));
    lean_closure_set(v___x_213_, 1, lean_box(0));
    lean_closure_set(v___x_213_, 2, v_x_209_);
    v___x_214_ = lean_apply_2(v_inst_208_, lean_box(0), v___x_213_);
    v___f_215_ = lean_alloc_closure(
        l_Lake_MonadError_runIO___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_215_, 0, v_inst_207_);
    lean_closure_set(v___f_215_, 1, v_toPure_212_);
    v___x_216_ = lean_apply_4(
        v_toBind_211_,
        lean_box(0),
        lean_box(0),
        v___x_214_,
        v___f_215_,
    );
    return v___x_216_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Error(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Error(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Error(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Error(builtin);
}

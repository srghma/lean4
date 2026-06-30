// Lean compiler output
// Module: Init.Control.Id
// Imports: Init.Control.MonadAttach
use crate::ffi::{lean_array_push, lean_array_to_list};
use crate::r#gen::Init::Control::MonadAttach::{
    initialize_Init_Control_MonadAttach, runtime_initialize_Init_Control_MonadAttach,
};
pub static l_Id_instMonad___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__0_value) as *mut leanh::LeanObject;
pub static l_Id_instMonad___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__1_value) as *mut leanh::LeanObject;
pub static l_Id_instMonad___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__2_value) as *mut leanh::LeanObject;
pub static l_Id_instMonad___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__3_value) as *mut leanh::LeanObject;
pub static l_Id_instMonad___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__4_value) as *mut leanh::LeanObject;
pub static l_Id_instMonad___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__5_value) as *mut leanh::LeanObject;
pub static l_Id_instMonad___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__6_value) as *mut leanh::LeanObject;
pub static l_Id_instMonad___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Id_instMonad___closed__0_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__1_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_Id_instMonad___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__7_value) as *mut leanh::LeanObject;
pub static l_Id_instMonad___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Id_instMonad___closed__7_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__2_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__3_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__4_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__5_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_Id_instMonad___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__8_value) as *mut leanh::LeanObject;
pub static l_Id_instMonad___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Id_instMonad___closed__8_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__6_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_Id_instMonad___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__9_value) as *mut leanh::LeanObject;
pub static mut l_Id_instMonad: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__9_value) as *mut leanh::LeanObject;
pub static mut l_Id_hasBind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__6_value) as *mut leanh::LeanObject;
pub static mut l_Id_instMonadAttach: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__2_value) as *mut leanh::LeanObject;
pub static l_ForIn_toArray___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ForIn_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ForIn_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ForIn_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_ForIn_toArray___redArg___closed__1_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_ForIn_toArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ForIn_toArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Id_instMonad___lam__0(
    mut v_00_u03b1_137_: *mut leanh::LeanObject,
    mut v_00_u03b2_138_: *mut leanh::LeanObject,
    mut v_f_139_: *mut leanh::LeanObject,
    mut v_x_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_141_ = leanh::lean_apply_1(v_f_139_, v_x_140_);
    return v___x_141_;
}
pub unsafe fn l_Id_instMonad___lam__1(
    mut v_00_u03b1_142_: *mut leanh::LeanObject,
    mut v_00_u03b2_143_: *mut leanh::LeanObject,
    mut v___y_144_: *mut leanh::LeanObject,
    mut v___y_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___y_144_);
    return v___y_144_;
}
pub unsafe fn l_Id_instMonad___lam__1___boxed(
    mut v_00_u03b1_146_: *mut leanh::LeanObject,
    mut v_00_u03b2_147_: *mut leanh::LeanObject,
    mut v___y_148_: *mut leanh::LeanObject,
    mut v___y_149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_150_ = l_Id_instMonad___lam__1(v_00_u03b1_146_, v_00_u03b2_147_, v___y_148_, v___y_149_);
    leanh::lean_dec(v___y_149_);
    leanh::lean_dec(v___y_148_);
    return v_res_150_;
}
pub unsafe fn l_Id_instMonad___lam__2(
    mut v_00_u03b1_151_: *mut leanh::LeanObject,
    mut v_x_152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_152_);
    return v_x_152_;
}
pub unsafe fn l_Id_instMonad___lam__2___boxed(
    mut v_00_u03b1_153_: *mut leanh::LeanObject,
    mut v_x_154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_155_ = l_Id_instMonad___lam__2(v_00_u03b1_153_, v_x_154_);
    leanh::lean_dec(v_x_154_);
    return v_res_155_;
}
pub unsafe fn l_Id_instMonad___lam__3(
    mut v_00_u03b1_156_: *mut leanh::LeanObject,
    mut v_00_u03b2_157_: *mut leanh::LeanObject,
    mut v_f_158_: *mut leanh::LeanObject,
    mut v_x_159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_160_ = leanh::lean_box(0);
    v___x_161_ = leanh::lean_apply_1(v_x_159_, v___x_160_);
    v___x_162_ = leanh::lean_apply_1(v_f_158_, v___x_161_);
    return v___x_162_;
}
pub unsafe fn l_Id_instMonad___lam__4(
    mut v_00_u03b1_163_: *mut leanh::LeanObject,
    mut v_00_u03b2_164_: *mut leanh::LeanObject,
    mut v_x_165_: *mut leanh::LeanObject,
    mut v_y_166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_165_);
    return v_x_165_;
}
pub unsafe fn l_Id_instMonad___lam__4___boxed(
    mut v_00_u03b1_167_: *mut leanh::LeanObject,
    mut v_00_u03b2_168_: *mut leanh::LeanObject,
    mut v_x_169_: *mut leanh::LeanObject,
    mut v_y_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_171_ = l_Id_instMonad___lam__4(v_00_u03b1_167_, v_00_u03b2_168_, v_x_169_, v_y_170_);
    leanh::lean_dec(v_y_170_);
    leanh::lean_dec(v_x_169_);
    return v_res_171_;
}
pub unsafe fn l_Id_instMonad___lam__5(
    mut v_00_u03b1_172_: *mut leanh::LeanObject,
    mut v_00_u03b2_173_: *mut leanh::LeanObject,
    mut v_x_174_: *mut leanh::LeanObject,
    mut v_y_175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_176_ = leanh::lean_box(0);
    v___x_177_ = leanh::lean_apply_1(v_y_175_, v___x_176_);
    return v___x_177_;
}
pub unsafe fn l_Id_instMonad___lam__5___boxed(
    mut v_00_u03b1_178_: *mut leanh::LeanObject,
    mut v_00_u03b2_179_: *mut leanh::LeanObject,
    mut v_x_180_: *mut leanh::LeanObject,
    mut v_y_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_182_ = l_Id_instMonad___lam__5(v_00_u03b1_178_, v_00_u03b2_179_, v_x_180_, v_y_181_);
    leanh::lean_dec(v_x_180_);
    return v_res_182_;
}
pub unsafe fn l_Id_instMonad___lam__6(
    mut v_00_u03b1_183_: *mut leanh::LeanObject,
    mut v_00_u03b2_184_: *mut leanh::LeanObject,
    mut v_x_185_: *mut leanh::LeanObject,
    mut v_f_186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_187_ = leanh::lean_apply_1(v_f_186_, v_x_185_);
    return v___x_187_;
}
pub unsafe fn l_Id_run___redArg(
    mut v_x_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_209_);
    return v_x_209_;
}
pub unsafe fn l_Id_run___redArg___boxed(
    mut v_x_210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_211_ = l_Id_run___redArg(v_x_210_);
    leanh::lean_dec(v_x_210_);
    return v_res_211_;
}
pub unsafe fn l_Id_run(
    mut v_00_u03b1_212_: *mut leanh::LeanObject,
    mut v_x_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_213_);
    return v_x_213_;
}
pub unsafe fn l_Id_run___boxed(
    mut v_00_u03b1_214_: *mut leanh::LeanObject,
    mut v_x_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Id_run(v_00_u03b1_214_, v_x_215_);
    leanh::lean_dec(v_x_215_);
    return v_res_216_;
}
pub unsafe fn l_Id_instOfNat___aux__1___redArg(
    mut v_inst_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_217_);
    return v_inst_217_;
}
pub unsafe fn l_Id_instOfNat___aux__1___redArg___boxed(
    mut v_inst_218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_219_ = l_Id_instOfNat___aux__1___redArg(v_inst_218_);
    leanh::lean_dec(v_inst_218_);
    return v_res_219_;
}
pub unsafe fn l_Id_instOfNat___aux__1(
    mut v_00_u03b1_220_: *mut leanh::LeanObject,
    mut v_n_221_: *mut leanh::LeanObject,
    mut v_inst_222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_222_);
    return v_inst_222_;
}
pub unsafe fn l_Id_instOfNat___aux__1___boxed(
    mut v_00_u03b1_223_: *mut leanh::LeanObject,
    mut v_n_224_: *mut leanh::LeanObject,
    mut v_inst_225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_226_ = l_Id_instOfNat___aux__1(v_00_u03b1_223_, v_n_224_, v_inst_225_);
    leanh::lean_dec(v_inst_225_);
    leanh::lean_dec(v_n_224_);
    return v_res_226_;
}
pub unsafe fn l_Id_instOfNat___redArg(
    mut v_inst_227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_227_);
    return v_inst_227_;
}
pub unsafe fn l_Id_instOfNat___redArg___boxed(
    mut v_inst_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l_Id_instOfNat___redArg(v_inst_228_);
    leanh::lean_dec(v_inst_228_);
    return v_res_229_;
}
pub unsafe fn l_Id_instOfNat(
    mut v_00_u03b1_230_: *mut leanh::LeanObject,
    mut v_n_231_: *mut leanh::LeanObject,
    mut v_inst_232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_232_);
    return v_inst_232_;
}
pub unsafe fn l_Id_instOfNat___boxed(
    mut v_00_u03b1_233_: *mut leanh::LeanObject,
    mut v_n_234_: *mut leanh::LeanObject,
    mut v_inst_235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Id_instOfNat(v_00_u03b1_233_, v_n_234_, v_inst_235_);
    leanh::lean_dec(v_inst_235_);
    leanh::lean_dec(v_n_234_);
    return v_res_236_;
}
pub unsafe fn l_Id_instMonadLiftTOfPure___redArg___lam__0(
    mut v_inst_237_: *mut leanh::LeanObject,
    mut v_00_u03b1_238_: *mut leanh::LeanObject,
    mut v_x_239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_240_ = leanh::lean_apply_2(v_inst_237_, leanh::lean_box(0), v_x_239_);
    return v___x_240_;
}
pub unsafe fn l_Id_instMonadLiftTOfPure___redArg(
    mut v_inst_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_242_ = leanh::lean_alloc_closure(
        l_Id_instMonadLiftTOfPure___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_242_, 0, v_inst_241_);
    return v___f_242_;
}
pub unsafe fn l_Id_instMonadLiftTOfPure(
    mut v_m_243_: *mut leanh::LeanObject,
    mut v_inst_244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_245_ = leanh::lean_alloc_closure(
        l_Id_instMonadLiftTOfPure___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_245_, 0, v_inst_244_);
    return v___f_245_;
}
pub unsafe fn l_ForIn_toArray___redArg___lam__0(
    mut v_a_247_: *mut leanh::LeanObject,
    mut v_acc_248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_249_ = lean_array_push(v_acc_248_, v_a_247_);
    v___x_250_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_250_, 0, v___x_249_);
    return v___x_250_;
}
pub unsafe fn l_ForIn_toArray___redArg(
    mut v_inst_254_: *mut leanh::LeanObject,
    mut v_xs_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_256_ = l_ForIn_toArray___redArg___closed__0;
    v___x_257_ = l_ForIn_toArray___redArg___closed__1;
    v___x_258_ = leanh::lean_apply_4(
        v_inst_254_,
        leanh::lean_box(0),
        v_xs_255_,
        v___x_257_,
        v___f_256_,
    );
    return v___x_258_;
}
pub unsafe fn l_ForIn_toArray(
    mut v_00_u03c1_259_: *mut leanh::LeanObject,
    mut v_00_u03b1_260_: *mut leanh::LeanObject,
    mut v_inst_261_: *mut leanh::LeanObject,
    mut v_xs_262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_263_ = l_ForIn_toArray___redArg(v_inst_261_, v_xs_262_);
    return v___x_263_;
}
pub unsafe fn l_ForIn_toList___redArg(
    mut v_inst_264_: *mut leanh::LeanObject,
    mut v_xs_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ = l_ForIn_toArray___redArg(v_inst_264_, v_xs_265_);
    v___x_267_ = lean_array_to_list(v___x_266_);
    return v___x_267_;
}
pub unsafe fn l_ForIn_toList(
    mut v_00_u03c1_268_: *mut leanh::LeanObject,
    mut v_00_u03b1_269_: *mut leanh::LeanObject,
    mut v_inst_270_: *mut leanh::LeanObject,
    mut v_xs_271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_272_ = l_ForIn_toList___redArg(v_inst_270_, v_xs_271_);
    return v___x_272_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Id(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_MonadAttach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Id(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Id(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_MonadAttach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Id(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Id(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Control_Id(builtin);
}
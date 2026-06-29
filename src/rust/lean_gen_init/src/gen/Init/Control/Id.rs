// Lean compiler output
// Module: Init.Control.Id
// Imports: Init.Control.MonadAttach
use crate::r#gen::Init::Control::MonadAttach::{
    initialize_Init_Control_MonadAttach, runtime_initialize_Init_Control_MonadAttach,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_array_to_list};
pub static l_Id_instMonad___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Id_instMonad___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Id_instMonad___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Id_instMonad___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Id_instMonad___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Id_instMonad___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Id_instMonad___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Id_instMonad___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Id_instMonad___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Id_instMonad___closed__0_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__1_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Id_instMonad___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Id_instMonad___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Id_instMonad___closed__7_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__2_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__3_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__4_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__5_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Id_instMonad___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Id_instMonad___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Id_instMonad___closed__8_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Id_instMonad___closed__6_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Id_instMonad___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__9_value) as *mut crate::leanh::LeanObject;
pub static mut l_Id_instMonad: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__9_value) as *mut crate::leanh::LeanObject;
pub static mut l_Id_hasBind: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__6_value) as *mut crate::leanh::LeanObject;
pub static mut l_Id_instMonadAttach: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Id_instMonad___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_ForIn_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_ForIn_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ForIn_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ForIn_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_ForIn_toArray___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_ForIn_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ForIn_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Id_instMonad___lam__0(
    mut v_00_u03b1_137_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_138_: *mut crate::leanh::LeanObject,
    mut v_f_139_: *mut crate::leanh::LeanObject,
    mut v_x_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_141_ = crate::leanh::lean_apply_1(v_f_139_, v_x_140_);
    return v___x_141_;
}
pub unsafe fn l_Id_instMonad___lam__1(
    mut v_00_u03b1_142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_143_: *mut crate::leanh::LeanObject,
    mut v___y_144_: *mut crate::leanh::LeanObject,
    mut v___y_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___y_144_);
    return v___y_144_;
}
pub unsafe fn l_Id_instMonad___lam__1___boxed(
    mut v_00_u03b1_146_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_147_: *mut crate::leanh::LeanObject,
    mut v___y_148_: *mut crate::leanh::LeanObject,
    mut v___y_149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_150_ = l_Id_instMonad___lam__1(v_00_u03b1_146_, v_00_u03b2_147_, v___y_148_, v___y_149_);
    crate::leanh::lean_dec(v___y_149_);
    crate::leanh::lean_dec(v___y_148_);
    return v_res_150_;
}
pub unsafe fn l_Id_instMonad___lam__2(
    mut v_00_u03b1_151_: *mut crate::leanh::LeanObject,
    mut v_x_152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_152_);
    return v_x_152_;
}
pub unsafe fn l_Id_instMonad___lam__2___boxed(
    mut v_00_u03b1_153_: *mut crate::leanh::LeanObject,
    mut v_x_154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_155_ = l_Id_instMonad___lam__2(v_00_u03b1_153_, v_x_154_);
    crate::leanh::lean_dec(v_x_154_);
    return v_res_155_;
}
pub unsafe fn l_Id_instMonad___lam__3(
    mut v_00_u03b1_156_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_157_: *mut crate::leanh::LeanObject,
    mut v_f_158_: *mut crate::leanh::LeanObject,
    mut v_x_159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_160_ = crate::leanh::lean_box(0);
    v___x_161_ = crate::leanh::lean_apply_1(v_x_159_, v___x_160_);
    v___x_162_ = crate::leanh::lean_apply_1(v_f_158_, v___x_161_);
    return v___x_162_;
}
pub unsafe fn l_Id_instMonad___lam__4(
    mut v_00_u03b1_163_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_164_: *mut crate::leanh::LeanObject,
    mut v_x_165_: *mut crate::leanh::LeanObject,
    mut v_y_166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_165_);
    return v_x_165_;
}
pub unsafe fn l_Id_instMonad___lam__4___boxed(
    mut v_00_u03b1_167_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_168_: *mut crate::leanh::LeanObject,
    mut v_x_169_: *mut crate::leanh::LeanObject,
    mut v_y_170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_171_ = l_Id_instMonad___lam__4(v_00_u03b1_167_, v_00_u03b2_168_, v_x_169_, v_y_170_);
    crate::leanh::lean_dec(v_y_170_);
    crate::leanh::lean_dec(v_x_169_);
    return v_res_171_;
}
pub unsafe fn l_Id_instMonad___lam__5(
    mut v_00_u03b1_172_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_173_: *mut crate::leanh::LeanObject,
    mut v_x_174_: *mut crate::leanh::LeanObject,
    mut v_y_175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_176_ = crate::leanh::lean_box(0);
    v___x_177_ = crate::leanh::lean_apply_1(v_y_175_, v___x_176_);
    return v___x_177_;
}
pub unsafe fn l_Id_instMonad___lam__5___boxed(
    mut v_00_u03b1_178_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_179_: *mut crate::leanh::LeanObject,
    mut v_x_180_: *mut crate::leanh::LeanObject,
    mut v_y_181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_182_ = l_Id_instMonad___lam__5(v_00_u03b1_178_, v_00_u03b2_179_, v_x_180_, v_y_181_);
    crate::leanh::lean_dec(v_x_180_);
    return v_res_182_;
}
pub unsafe fn l_Id_instMonad___lam__6(
    mut v_00_u03b1_183_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_184_: *mut crate::leanh::LeanObject,
    mut v_x_185_: *mut crate::leanh::LeanObject,
    mut v_f_186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_187_ = crate::leanh::lean_apply_1(v_f_186_, v_x_185_);
    return v___x_187_;
}
pub unsafe fn l_Id_run___redArg(
    mut v_x_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_209_);
    return v_x_209_;
}
pub unsafe fn l_Id_run___redArg___boxed(
    mut v_x_210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_211_ = l_Id_run___redArg(v_x_210_);
    crate::leanh::lean_dec(v_x_210_);
    return v_res_211_;
}
pub unsafe fn l_Id_run(
    mut v_00_u03b1_212_: *mut crate::leanh::LeanObject,
    mut v_x_213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_213_);
    return v_x_213_;
}
pub unsafe fn l_Id_run___boxed(
    mut v_00_u03b1_214_: *mut crate::leanh::LeanObject,
    mut v_x_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Id_run(v_00_u03b1_214_, v_x_215_);
    crate::leanh::lean_dec(v_x_215_);
    return v_res_216_;
}
pub unsafe fn l_Id_instOfNat___aux__1___redArg(
    mut v_inst_217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_217_);
    return v_inst_217_;
}
pub unsafe fn l_Id_instOfNat___aux__1___redArg___boxed(
    mut v_inst_218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_219_ = l_Id_instOfNat___aux__1___redArg(v_inst_218_);
    crate::leanh::lean_dec(v_inst_218_);
    return v_res_219_;
}
pub unsafe fn l_Id_instOfNat___aux__1(
    mut v_00_u03b1_220_: *mut crate::leanh::LeanObject,
    mut v_n_221_: *mut crate::leanh::LeanObject,
    mut v_inst_222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_222_);
    return v_inst_222_;
}
pub unsafe fn l_Id_instOfNat___aux__1___boxed(
    mut v_00_u03b1_223_: *mut crate::leanh::LeanObject,
    mut v_n_224_: *mut crate::leanh::LeanObject,
    mut v_inst_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_226_ = l_Id_instOfNat___aux__1(v_00_u03b1_223_, v_n_224_, v_inst_225_);
    crate::leanh::lean_dec(v_inst_225_);
    crate::leanh::lean_dec(v_n_224_);
    return v_res_226_;
}
pub unsafe fn l_Id_instOfNat___redArg(
    mut v_inst_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_227_);
    return v_inst_227_;
}
pub unsafe fn l_Id_instOfNat___redArg___boxed(
    mut v_inst_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l_Id_instOfNat___redArg(v_inst_228_);
    crate::leanh::lean_dec(v_inst_228_);
    return v_res_229_;
}
pub unsafe fn l_Id_instOfNat(
    mut v_00_u03b1_230_: *mut crate::leanh::LeanObject,
    mut v_n_231_: *mut crate::leanh::LeanObject,
    mut v_inst_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_232_);
    return v_inst_232_;
}
pub unsafe fn l_Id_instOfNat___boxed(
    mut v_00_u03b1_233_: *mut crate::leanh::LeanObject,
    mut v_n_234_: *mut crate::leanh::LeanObject,
    mut v_inst_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Id_instOfNat(v_00_u03b1_233_, v_n_234_, v_inst_235_);
    crate::leanh::lean_dec(v_inst_235_);
    crate::leanh::lean_dec(v_n_234_);
    return v_res_236_;
}
pub unsafe fn l_Id_instMonadLiftTOfPure___redArg___lam__0(
    mut v_inst_237_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_238_: *mut crate::leanh::LeanObject,
    mut v_x_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_240_ = crate::leanh::lean_apply_2(v_inst_237_, crate::leanh::lean_box(0), v_x_239_);
    return v___x_240_;
}
pub unsafe fn l_Id_instMonadLiftTOfPure___redArg(
    mut v_inst_241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_242_ = crate::leanh::lean_alloc_closure(
        l_Id_instMonadLiftTOfPure___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_242_, 0, v_inst_241_);
    return v___f_242_;
}
pub unsafe fn l_Id_instMonadLiftTOfPure(
    mut v_m_243_: *mut crate::leanh::LeanObject,
    mut v_inst_244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_245_ = crate::leanh::lean_alloc_closure(
        l_Id_instMonadLiftTOfPure___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_245_, 0, v_inst_244_);
    return v___f_245_;
}
pub unsafe fn l_ForIn_toArray___redArg___lam__0(
    mut v_a_247_: *mut crate::leanh::LeanObject,
    mut v_acc_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_249_ = lean_array_push(v_acc_248_, v_a_247_);
    v___x_250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_250_, 0, v___x_249_);
    return v___x_250_;
}
pub unsafe fn l_ForIn_toArray___redArg(
    mut v_inst_254_: *mut crate::leanh::LeanObject,
    mut v_xs_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_256_ = l_ForIn_toArray___redArg___closed__0;
    v___x_257_ = l_ForIn_toArray___redArg___closed__1;
    v___x_258_ = crate::leanh::lean_apply_4(
        v_inst_254_,
        crate::leanh::lean_box(0),
        v_xs_255_,
        v___x_257_,
        v___f_256_,
    );
    return v___x_258_;
}
pub unsafe fn l_ForIn_toArray(
    mut v_00_u03c1_259_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_260_: *mut crate::leanh::LeanObject,
    mut v_inst_261_: *mut crate::leanh::LeanObject,
    mut v_xs_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_263_ = l_ForIn_toArray___redArg(v_inst_261_, v_xs_262_);
    return v___x_263_;
}
pub unsafe fn l_ForIn_toList___redArg(
    mut v_inst_264_: *mut crate::leanh::LeanObject,
    mut v_xs_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ = l_ForIn_toArray___redArg(v_inst_264_, v_xs_265_);
    v___x_267_ = lean_array_to_list(v___x_266_);
    return v___x_267_;
}
pub unsafe fn l_ForIn_toList(
    mut v_00_u03c1_268_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_269_: *mut crate::leanh::LeanObject,
    mut v_inst_270_: *mut crate::leanh::LeanObject,
    mut v_xs_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_272_ = l_ForIn_toList___redArg(v_inst_270_, v_xs_271_);
    return v___x_272_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Id(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_MonadAttach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Id(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Id(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_MonadAttach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_Id(builtin);
}

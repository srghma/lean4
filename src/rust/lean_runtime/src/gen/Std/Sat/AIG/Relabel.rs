// Lean compiler output
// Module: Std.Sat.AIG.Relabel
// Imports: Std.Sat.AIG.Lemmas Init.ByCases Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::Lemmas::{
    initialize_Std_Sat_AIG_Lemmas, runtime_initialize_Std_Sat_AIG_Lemmas,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_mk_array};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Std_Sat_AIG_relabel___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_Sat_AIG_relabel___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__7_value) as *mut LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Std_Sat_AIG_relabel___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_Sat_AIG_relabel___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__9_value) as *mut LeanObject;
static mut l_Std_Sat_AIG_relabel___redArg___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Sat_AIG_relabel___redArg___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Sat_AIG_relabel___redArg___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Sat_AIG_relabel___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Sat_AIG_Decl_relabel___redArg(
    mut v_r_153_: *mut LeanObject,
    mut v_decl_154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_159_: u8 = 0;
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_164_: u8 = 0;
    let mut v_l_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_169_: u8 = 0;
    let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_decl_154_) {
                0 => {
                    lean_dec(v_r_153_);
                    v___x_155_ = lean_box(0);
                    return v___x_155_;
                }
                1 => {
                    v_idx_156_ = lean_ctor_get(v_decl_154_, 0);
                    v_isSharedCheck_164_ = (!lean_is_exclusive(v_decl_154_)) as u8;
                    if v_isSharedCheck_164_ == 0 {
                        v___x_158_ = v_decl_154_;
                        v_isShared_159_ = v_isSharedCheck_164_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_idx_156_);
                        lean_dec(v_decl_154_);
                        v___x_158_ = lean_box(0);
                        v_isShared_159_ = v_isSharedCheck_164_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_r_153_);
                    v_l_165_ = lean_ctor_get(v_decl_154_, 0);
                    v_r_166_ = lean_ctor_get(v_decl_154_, 1);
                    v_isSharedCheck_173_ = (!lean_is_exclusive(v_decl_154_)) as u8;
                    if v_isSharedCheck_173_ == 0 {
                        v___x_168_ = v_decl_154_;
                        v_isShared_169_ = v_isSharedCheck_173_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_r_166_);
                        lean_inc(v_l_165_);
                        lean_dec(v_decl_154_);
                        v___x_168_ = lean_box(0);
                        v_isShared_169_ = v_isSharedCheck_173_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_160_ = lean_apply_1(v_r_153_, v_idx_156_);
                if v_isShared_159_ == 0 {
                    lean_ctor_set(v___x_158_, 0, v___x_160_);
                    v___x_162_ = v___x_158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
                    v___x_162_ = v_reuseFailAlloc_163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_162_;
            }
            3 => {
                if v_isShared_169_ == 0 {
                    v___x_171_ = v___x_168_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_172_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_172_, 0, v_l_165_);
                    lean_ctor_set(v_reuseFailAlloc_172_, 1, v_r_166_);
                    v___x_171_ = v_reuseFailAlloc_172_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Decl_relabel(
    mut v_00_u03b1_174_: *mut LeanObject,
    mut v_00_u03b2_175_: *mut LeanObject,
    mut v_r_176_: *mut LeanObject,
    mut v_decl_177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    v___x_178_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_176_, v_decl_177_);
    return v___x_178_;
}
pub unsafe fn l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___redArg(
    mut v_decl_179_: *mut LeanObject,
    mut v_h__1_180_: *mut LeanObject,
    mut v_h__2_181_: *mut LeanObject,
    mut v_h__3_182_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_179_) {
        0 => {
            let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_182_);
            lean_dec(v_h__2_181_);
            v___x_183_ = lean_box(0);
            v___x_184_ = lean_apply_1(v_h__1_180_, v___x_183_);
            return v___x_184_;
        }
        1 => {
            let mut v_idx_185_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_182_);
            lean_dec(v_h__1_180_);
            v_idx_185_ = lean_ctor_get(v_decl_179_, 0);
            lean_inc(v_idx_185_);
            lean_dec_ref_known(v_decl_179_, 1);
            v___x_186_ = lean_apply_1(v_h__2_181_, v_idx_185_);
            return v___x_186_;
        }
        _ => {
            let mut v_l_187_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_188_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_181_);
            lean_dec(v_h__1_180_);
            v_l_187_ = lean_ctor_get(v_decl_179_, 0);
            lean_inc(v_l_187_);
            v_r_188_ = lean_ctor_get(v_decl_179_, 1);
            lean_inc(v_r_188_);
            lean_dec_ref_known(v_decl_179_, 2);
            v___x_189_ = lean_apply_2(v_h__3_182_, v_l_187_, v_r_188_);
            return v___x_189_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter(
    mut v_00_u03b1_190_: *mut LeanObject,
    mut v_motive_191_: *mut LeanObject,
    mut v_decl_192_: *mut LeanObject,
    mut v_h__1_193_: *mut LeanObject,
    mut v_h__2_194_: *mut LeanObject,
    mut v_h__3_195_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_192_) {
        0 => {
            let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_195_);
            lean_dec(v_h__2_194_);
            v___x_196_ = lean_box(0);
            v___x_197_ = lean_apply_1(v_h__1_193_, v___x_196_);
            return v___x_197_;
        }
        1 => {
            let mut v_idx_198_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_195_);
            lean_dec(v_h__1_193_);
            v_idx_198_ = lean_ctor_get(v_decl_192_, 0);
            lean_inc(v_idx_198_);
            lean_dec_ref_known(v_decl_192_, 1);
            v___x_199_ = lean_apply_1(v_h__2_194_, v_idx_198_);
            return v___x_199_;
        }
        _ => {
            let mut v_l_200_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_201_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_194_);
            lean_dec(v_h__1_193_);
            v_l_200_ = lean_ctor_get(v_decl_192_, 0);
            lean_inc(v_l_200_);
            v_r_201_ = lean_ctor_get(v_decl_192_, 1);
            lean_inc(v_r_201_);
            lean_dec_ref_known(v_decl_192_, 2);
            v___x_202_ = lean_apply_2(v_h__3_195_, v_l_200_, v_r_201_);
            return v___x_202_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_relabel___redArg___lam__0(
    mut v_r_203_: *mut LeanObject,
    mut v_x_204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    v___x_205_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_203_, v_x_204_);
    return v___x_205_;
}
pub unsafe fn _init_l_Std_Sat_AIG_relabel___redArg___closed__10() -> *mut LeanObject {
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    v___x_225_ = lean_box(0);
    v___x_226_ = lean_unsigned_to_nat(16);
    v___x_227_ = lean_mk_array(v___x_226_, v___x_225_);
    return v___x_227_;
}
pub unsafe fn _init_l_Std_Sat_AIG_relabel___redArg___closed__11() -> *mut LeanObject {
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_230_: *mut LeanObject = core::ptr::null_mut();
    v___x_228_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___redArg___closed__10_once),
        _init_l_Std_Sat_AIG_relabel___redArg___closed__10,
    );
    v___x_229_ = lean_unsigned_to_nat(0);
    v_cache_230_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_cache_230_, 0, v___x_229_);
    lean_ctor_set(v_cache_230_, 1, v___x_228_);
    return v_cache_230_;
}
pub unsafe fn l_Std_Sat_AIG_relabel___redArg(
    mut v_r_231_: *mut LeanObject,
    mut v_aig_232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_236_: u8 = 0;
    let mut v___f_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_239_: usize = 0;
    let mut v___x_240_: usize = 0;
    let mut v_decls_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_246_: u8 = 0;
    let mut v_unused_247_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_233_ = lean_ctor_get(v_aig_232_, 0);
                v_isSharedCheck_246_ = (!lean_is_exclusive(v_aig_232_)) as u8;
                if v_isSharedCheck_246_ == 0 {
                    v_unused_247_ = lean_ctor_get(v_aig_232_, 1);
                    lean_dec(v_unused_247_);
                    v___x_235_ = v_aig_232_;
                    v_isShared_236_ = v_isSharedCheck_246_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_decls_233_);
                    lean_dec(v_aig_232_);
                    v___x_235_ = lean_box(0);
                    v_isShared_236_ = v_isSharedCheck_246_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_237_ = lean_alloc_closure(
                    l_Std_Sat_AIG_relabel___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_237_, 0, v_r_231_);
                v___x_238_ = l_Std_Sat_AIG_relabel___redArg___closed__9;
                v_sz_239_ = lean_array_size(v_decls_233_);
                v___x_240_ = 0usize;
                v_decls_241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_238_,
                    v___f_237_,
                    v_sz_239_,
                    v___x_240_,
                    v_decls_233_,
                );
                v_cache_242_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___redArg___closed__11),
                    core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___redArg___closed__11_once),
                    _init_l_Std_Sat_AIG_relabel___redArg___closed__11,
                );
                if v_isShared_236_ == 0 {
                    lean_ctor_set(v___x_235_, 1, v_cache_242_);
                    lean_ctor_set(v___x_235_, 0, v_decls_241_);
                    v___x_244_ = v___x_235_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_245_, 0, v_decls_241_);
                    lean_ctor_set(v_reuseFailAlloc_245_, 1, v_cache_242_);
                    v___x_244_ = v_reuseFailAlloc_245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_relabel(
    mut v_00_u03b1_248_: *mut LeanObject,
    mut v_inst_249_: *mut LeanObject,
    mut v_inst_250_: *mut LeanObject,
    mut v_00_u03b2_251_: *mut LeanObject,
    mut v_inst_252_: *mut LeanObject,
    mut v_inst_253_: *mut LeanObject,
    mut v_r_254_: *mut LeanObject,
    mut v_aig_255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    v___x_256_ = l_Std_Sat_AIG_relabel___redArg(v_r_254_, v_aig_255_);
    return v___x_256_;
}
pub unsafe fn l_Std_Sat_AIG_relabel___boxed(
    mut v_00_u03b1_257_: *mut LeanObject,
    mut v_inst_258_: *mut LeanObject,
    mut v_inst_259_: *mut LeanObject,
    mut v_00_u03b2_260_: *mut LeanObject,
    mut v_inst_261_: *mut LeanObject,
    mut v_inst_262_: *mut LeanObject,
    mut v_r_263_: *mut LeanObject,
    mut v_aig_264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_265_: *mut LeanObject = core::ptr::null_mut();
    v_res_265_ = l_Std_Sat_AIG_relabel(
        v_00_u03b1_257_,
        v_inst_258_,
        v_inst_259_,
        v_00_u03b2_260_,
        v_inst_261_,
        v_inst_262_,
        v_r_263_,
        v_aig_264_,
    );
    lean_dec_ref(v_inst_262_);
    lean_dec_ref(v_inst_261_);
    lean_dec_ref(v_inst_259_);
    lean_dec_ref(v_inst_258_);
    return v_res_265_;
}
pub unsafe fn l_Std_Sat_AIG_Entrypoint_relabel___redArg(
    mut v_r_266_: *mut LeanObject,
    mut v_entry_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_272_: u8 = 0;
    let mut v_gate_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_274_: u8 = 0;
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_277_: u8 = 0;
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_285_: u8 = 0;
    let mut v_isSharedCheck_286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_268_ = lean_ctor_get(v_entry_267_, 1);
                v_aig_269_ = lean_ctor_get(v_entry_267_, 0);
                v_isSharedCheck_286_ = (!lean_is_exclusive(v_entry_267_)) as u8;
                if v_isSharedCheck_286_ == 0 {
                    v___x_271_ = v_entry_267_;
                    v_isShared_272_ = v_isSharedCheck_286_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ref_268_);
                    lean_inc(v_aig_269_);
                    lean_dec(v_entry_267_);
                    v___x_271_ = lean_box(0);
                    v_isShared_272_ = v_isSharedCheck_286_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_273_ = lean_ctor_get(v_ref_268_, 0);
                v_invert_274_ = lean_ctor_get_uint8(
                    v_ref_268_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_285_ = (!lean_is_exclusive(v_ref_268_)) as u8;
                if v_isSharedCheck_285_ == 0 {
                    v___x_276_ = v_ref_268_;
                    v_isShared_277_ = v_isSharedCheck_285_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_gate_273_);
                    lean_dec(v_ref_268_);
                    v___x_276_ = lean_box(0);
                    v_isShared_277_ = v_isSharedCheck_285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_278_ = l_Std_Sat_AIG_relabel___redArg(v_r_266_, v_aig_269_);
                if v_isShared_277_ == 0 {
                    v___x_280_ = v___x_276_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_284_, 0, v_gate_273_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_284_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_invert_274_,
                    );
                    v___x_280_ = v_reuseFailAlloc_284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_272_ == 0 {
                    lean_ctor_set(v___x_271_, 1, v___x_280_);
                    lean_ctor_set(v___x_271_, 0, v___x_278_);
                    v___x_282_ = v___x_271_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_278_);
                    lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_280_);
                    v___x_282_ = v_reuseFailAlloc_283_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Entrypoint_relabel(
    mut v_00_u03b1_287_: *mut LeanObject,
    mut v_inst_288_: *mut LeanObject,
    mut v_inst_289_: *mut LeanObject,
    mut v_00_u03b2_290_: *mut LeanObject,
    mut v_inst_291_: *mut LeanObject,
    mut v_inst_292_: *mut LeanObject,
    mut v_r_293_: *mut LeanObject,
    mut v_entry_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    v___x_295_ = l_Std_Sat_AIG_Entrypoint_relabel___redArg(v_r_293_, v_entry_294_);
    return v___x_295_;
}
pub unsafe fn l_Std_Sat_AIG_Entrypoint_relabel___boxed(
    mut v_00_u03b1_296_: *mut LeanObject,
    mut v_inst_297_: *mut LeanObject,
    mut v_inst_298_: *mut LeanObject,
    mut v_00_u03b2_299_: *mut LeanObject,
    mut v_inst_300_: *mut LeanObject,
    mut v_inst_301_: *mut LeanObject,
    mut v_r_302_: *mut LeanObject,
    mut v_entry_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_304_: *mut LeanObject = core::ptr::null_mut();
    v_res_304_ = l_Std_Sat_AIG_Entrypoint_relabel(
        v_00_u03b1_296_,
        v_inst_297_,
        v_inst_298_,
        v_00_u03b2_299_,
        v_inst_300_,
        v_inst_301_,
        v_r_302_,
        v_entry_303_,
    );
    lean_dec_ref(v_inst_301_);
    lean_dec_ref(v_inst_300_);
    lean_dec_ref(v_inst_298_);
    lean_dec_ref(v_inst_297_);
    return v_res_304_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_Relabel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
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
pub unsafe fn meta_initialize_Std_Sat_AIG_Relabel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_Relabel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_Relabel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_Relabel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sat_AIG_Relabel(builtin);
}

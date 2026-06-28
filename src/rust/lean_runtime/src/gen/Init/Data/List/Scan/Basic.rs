// Lean compiler output
// Module: Init.Data.List.Scan.Basic
// Imports: Init.Data.List.Basic Init.Control.Id
use crate::r#gen::Init::Control::Id::{
    initialize_Init_Control_Id, l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed,
    l_Id_instMonad___lam__2___boxed, l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed,
    l_Id_instMonad___lam__5___boxed, l_Id_instMonad___lam__6, runtime_initialize_Init_Control_Id,
};
use crate::r#gen::Init::Core::l_flip;
use crate::r#gen::Init::Data::List::Basic::{
    initialize_Init_Data_List_Basic, l_List_reverse, l_List_reverse___redArg,
    runtime_initialize_Init_Data_List_Basic,
};
pub static l_List_scanlM___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_reverse as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_List_scanlM___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanlM___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_scanl___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_scanl___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanl___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_scanl___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_scanl___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanl___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_scanl___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_scanl___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanl___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_scanl___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_scanl___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanl___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List_scanl___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_scanl___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanl___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List_scanl___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_scanl___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanl___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_scanl___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_scanl___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanl___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List_scanl___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_List_scanl___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_scanl___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_scanl___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanl___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_List_scanl___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_List_scanl___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_scanl___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_scanl___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_scanl___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_scanl___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_scanl___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanl___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_List_scanl___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_List_scanl___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_scanl___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_scanl___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_scanl___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
    mut v_inst_162_: *mut crate::leanh::LeanObject,
    mut v_f_163_: *mut crate::leanh::LeanObject,
    mut v_a_164_: *mut crate::leanh::LeanObject,
    mut v_a_165_: *mut crate::leanh::LeanObject,
    mut v_a_166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_170_: u8 = 0;
    let mut v_toPure_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_176_: u8 = 0;
    let mut v_unused_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_164_) == 0 {
                    v_toApplicative_167_ = crate::leanh::lean_ctor_get(v_inst_162_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_167_);
                    crate::leanh::lean_dec(v_f_163_);
                    v_isSharedCheck_176_ = (!crate::leanh::lean_is_exclusive(v_inst_162_)) as u8;
                    if v_isSharedCheck_176_ == 0 {
                        v_unused_177_ = crate::leanh::lean_ctor_get(v_inst_162_, 1);
                        crate::leanh::lean_dec(v_unused_177_);
                        v_unused_178_ = crate::leanh::lean_ctor_get(v_inst_162_, 0);
                        crate::leanh::lean_dec(v_unused_178_);
                        v___x_169_ = v_inst_162_;
                        v_isShared_170_ = v_isSharedCheck_176_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_inst_162_);
                        v___x_169_ = crate::leanh::lean_box(0);
                        v_isShared_170_ = v_isSharedCheck_176_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_toBind_179_ = crate::leanh::lean_ctor_get(v_inst_162_, 1);
                    crate::leanh::lean_inc(v_toBind_179_);
                    v_head_180_ = crate::leanh::lean_ctor_get(v_a_164_, 0);
                    crate::leanh::lean_inc(v_head_180_);
                    v_tail_181_ = crate::leanh::lean_ctor_get(v_a_164_, 1);
                    crate::leanh::lean_inc(v_tail_181_);
                    crate::leanh::lean_dec_ref_known(v_a_164_, 2);
                    crate::leanh::lean_inc(v_f_163_);
                    crate::leanh::lean_inc(v_a_165_);
                    v___f_182_ = crate::leanh::lean_alloc_closure(
                        l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg___lam__0
                            as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_182_, 0, v_a_165_);
                    crate::leanh::lean_closure_set(v___f_182_, 1, v_a_166_);
                    crate::leanh::lean_closure_set(v___f_182_, 2, v_inst_162_);
                    crate::leanh::lean_closure_set(v___f_182_, 3, v_f_163_);
                    crate::leanh::lean_closure_set(v___f_182_, 4, v_tail_181_);
                    v___x_183_ = crate::leanh::lean_apply_2(v_f_163_, v_a_165_, v_head_180_);
                    v___x_184_ = crate::leanh::lean_apply_4(
                        v_toBind_179_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_183_,
                        v___f_182_,
                    );
                    return v___x_184_;
                }
            }
            1 => {
                v_toPure_171_ = crate::leanh::lean_ctor_get(v_toApplicative_167_, 1);
                crate::leanh::lean_inc(v_toPure_171_);
                crate::leanh::lean_dec_ref(v_toApplicative_167_);
                if v_isShared_170_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_169_, 1);
                    crate::leanh::lean_ctor_set(v___x_169_, 1, v_a_166_);
                    crate::leanh::lean_ctor_set(v___x_169_, 0, v_a_165_);
                    v___x_173_ = v___x_169_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_175_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_175_, 1, v_a_166_);
                    v___x_173_ = v_reuseFailAlloc_175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_174_ = crate::leanh::lean_apply_2(
                    v_toPure_171_,
                    crate::leanh::lean_box(0),
                    v___x_173_,
                );
                return v___x_174_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg___lam__0(
    mut v_a_185_: *mut crate::leanh::LeanObject,
    mut v_a_186_: *mut crate::leanh::LeanObject,
    mut v_inst_187_: *mut crate::leanh::LeanObject,
    mut v_f_188_: *mut crate::leanh::LeanObject,
    mut v_tail_189_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_191_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_191_, 0, v_a_185_);
    crate::leanh::lean_ctor_set(v___x_191_, 1, v_a_186_);
    v___x_192_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v_inst_187_,
        v_f_188_,
        v_tail_189_,
        v_____do__lift_190_,
        v___x_191_,
    );
    return v___x_192_;
}
pub unsafe fn l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go(
    mut v_m_193_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_194_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_195_: *mut crate::leanh::LeanObject,
    mut v_inst_196_: *mut crate::leanh::LeanObject,
    mut v_f_197_: *mut crate::leanh::LeanObject,
    mut v_a_198_: *mut crate::leanh::LeanObject,
    mut v_a_199_: *mut crate::leanh::LeanObject,
    mut v_a_200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_201_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v_inst_196_,
        v_f_197_,
        v_a_198_,
        v_a_199_,
        v_a_200_,
    );
    return v___x_201_;
}
pub unsafe fn l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM___redArg(
    mut v_inst_202_: *mut crate::leanh::LeanObject,
    mut v_f_203_: *mut crate::leanh::LeanObject,
    mut v_init_204_: *mut crate::leanh::LeanObject,
    mut v_l_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_206_ = crate::leanh::lean_box(0);
    v___x_207_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v_inst_202_,
        v_f_203_,
        v_l_205_,
        v_init_204_,
        v___x_206_,
    );
    return v___x_207_;
}
pub unsafe fn l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM(
    mut v_m_208_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_209_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_210_: *mut crate::leanh::LeanObject,
    mut v_inst_211_: *mut crate::leanh::LeanObject,
    mut v_f_212_: *mut crate::leanh::LeanObject,
    mut v_init_213_: *mut crate::leanh::LeanObject,
    mut v_l_214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_215_ = crate::leanh::lean_box(0);
    v___x_216_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v_inst_211_,
        v_f_212_,
        v_l_214_,
        v_init_213_,
        v___x_215_,
    );
    return v___x_216_;
}
pub unsafe fn l_List_scanlM___redArg(
    mut v_inst_218_: *mut crate::leanh::LeanObject,
    mut v_f_219_: *mut crate::leanh::LeanObject,
    mut v_init_220_: *mut crate::leanh::LeanObject,
    mut v_l_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_222_ = crate::leanh::lean_ctor_get(v_inst_218_, 0);
    v_toFunctor_223_ = crate::leanh::lean_ctor_get(v_toApplicative_222_, 0);
    v_map_224_ = crate::leanh::lean_ctor_get(v_toFunctor_223_, 0);
    crate::leanh::lean_inc(v_map_224_);
    v___x_225_ = l_List_scanlM___redArg___closed__0;
    v___x_226_ = crate::leanh::lean_box(0);
    v___x_227_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v_inst_218_,
        v_f_219_,
        v_l_221_,
        v_init_220_,
        v___x_226_,
    );
    v___x_228_ = crate::leanh::lean_apply_4(
        v_map_224_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_225_,
        v___x_227_,
    );
    return v___x_228_;
}
pub unsafe fn l_List_scanlM(
    mut v_m_229_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_230_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_231_: *mut crate::leanh::LeanObject,
    mut v_inst_232_: *mut crate::leanh::LeanObject,
    mut v_f_233_: *mut crate::leanh::LeanObject,
    mut v_init_234_: *mut crate::leanh::LeanObject,
    mut v_l_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_236_ = crate::leanh::lean_ctor_get(v_inst_232_, 0);
    v_toFunctor_237_ = crate::leanh::lean_ctor_get(v_toApplicative_236_, 0);
    v_map_238_ = crate::leanh::lean_ctor_get(v_toFunctor_237_, 0);
    crate::leanh::lean_inc(v_map_238_);
    v___x_239_ = l_List_scanlM___redArg___closed__0;
    v___x_240_ = crate::leanh::lean_box(0);
    v___x_241_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v_inst_232_,
        v_f_233_,
        v_l_235_,
        v_init_234_,
        v___x_240_,
    );
    v___x_242_ = crate::leanh::lean_apply_4(
        v_map_238_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_239_,
        v___x_241_,
    );
    return v___x_242_;
}
pub unsafe fn l_List_scanrM___redArg(
    mut v_inst_243_: *mut crate::leanh::LeanObject,
    mut v_f_244_: *mut crate::leanh::LeanObject,
    mut v_init_245_: *mut crate::leanh::LeanObject,
    mut v_xs_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = crate::leanh::lean_alloc_closure(l_flip as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_247_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_247_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_247_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_247_, 3, v_f_244_);
    v___x_248_ = l_List_reverse___redArg(v_xs_246_);
    v___x_249_ = crate::leanh::lean_box(0);
    v___x_250_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v_inst_243_,
        v___x_247_,
        v___x_248_,
        v_init_245_,
        v___x_249_,
    );
    return v___x_250_;
}
pub unsafe fn l_List_scanrM(
    mut v_m_251_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_252_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_253_: *mut crate::leanh::LeanObject,
    mut v_inst_254_: *mut crate::leanh::LeanObject,
    mut v_f_255_: *mut crate::leanh::LeanObject,
    mut v_init_256_: *mut crate::leanh::LeanObject,
    mut v_xs_257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_258_ = crate::leanh::lean_alloc_closure(l_flip as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_258_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_258_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_258_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_258_, 3, v_f_255_);
    v___x_259_ = l_List_reverse___redArg(v_xs_257_);
    v___x_260_ = crate::leanh::lean_box(0);
    v___x_261_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v_inst_254_,
        v___x_258_,
        v___x_259_,
        v_init_256_,
        v___x_260_,
    );
    return v___x_261_;
}
pub unsafe fn l_List_scanl___redArg___lam__0(
    mut v_f_262_: *mut crate::leanh::LeanObject,
    mut v_x1_263_: *mut crate::leanh::LeanObject,
    mut v_x2_264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_265_ = crate::leanh::lean_apply_2(v_f_262_, v_x1_263_, v_x2_264_);
    return v___x_265_;
}
pub unsafe fn l_List_scanl___redArg(
    mut v_f_285_: *mut crate::leanh::LeanObject,
    mut v_init_286_: *mut crate::leanh::LeanObject,
    mut v_as_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_288_ = crate::leanh::lean_alloc_closure(
        l_List_scanl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_288_, 0, v_f_285_);
    v___x_289_ = l_List_scanl___redArg___closed__9;
    v___x_290_ = crate::leanh::lean_box(0);
    v___x_291_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v___x_289_,
        v___f_288_,
        v_as_287_,
        v_init_286_,
        v___x_290_,
    );
    v___x_292_ = l_List_reverse___redArg(v___x_291_);
    return v___x_292_;
}
pub unsafe fn l_List_scanl(
    mut v_00_u03b2_293_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_294_: *mut crate::leanh::LeanObject,
    mut v_f_295_: *mut crate::leanh::LeanObject,
    mut v_init_296_: *mut crate::leanh::LeanObject,
    mut v_as_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_298_ = crate::leanh::lean_alloc_closure(
        l_List_scanl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_298_, 0, v_f_295_);
    v___x_299_ = l_List_scanl___redArg___closed__9;
    v___x_300_ = crate::leanh::lean_box(0);
    v___x_301_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v___x_299_,
        v___f_298_,
        v_as_297_,
        v_init_296_,
        v___x_300_,
    );
    v___x_302_ = l_List_reverse___redArg(v___x_301_);
    return v___x_302_;
}
pub unsafe fn l_List_scanr___redArg(
    mut v_f_303_: *mut crate::leanh::LeanObject,
    mut v_init_304_: *mut crate::leanh::LeanObject,
    mut v_as_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_306_ = crate::leanh::lean_alloc_closure(
        l_List_scanl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_306_, 0, v_f_303_);
    v___x_307_ = l_List_scanl___redArg___closed__9;
    v___x_308_ = crate::leanh::lean_alloc_closure(l_flip as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_308_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_308_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_308_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_308_, 3, v___f_306_);
    v___x_309_ = l_List_reverse___redArg(v_as_305_);
    v___x_310_ = crate::leanh::lean_box(0);
    v___x_311_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v___x_307_,
        v___x_308_,
        v___x_309_,
        v_init_304_,
        v___x_310_,
    );
    return v___x_311_;
}
pub unsafe fn l_List_scanr(
    mut v_00_u03b1_312_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_313_: *mut crate::leanh::LeanObject,
    mut v_f_314_: *mut crate::leanh::LeanObject,
    mut v_init_315_: *mut crate::leanh::LeanObject,
    mut v_as_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_317_ = crate::leanh::lean_alloc_closure(
        l_List_scanl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_317_, 0, v_f_314_);
    v___x_318_ = l_List_scanl___redArg___closed__9;
    v___x_319_ = crate::leanh::lean_alloc_closure(l_flip as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_319_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_319_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_319_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_319_, 3, v___f_317_);
    v___x_320_ = l_List_reverse___redArg(v_as_316_);
    v___x_321_ = crate::leanh::lean_box(0);
    v___x_322_ = l___private_Init_Data_List_Scan_Basic_0__List_scanAuxM_go___redArg(
        v___x_318_,
        v___x_319_,
        v___x_320_,
        v_init_315_,
        v___x_321_,
    );
    return v___x_322_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Scan_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Scan_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Scan_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Scan_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Scan_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Scan_Basic(builtin);
}

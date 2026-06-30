// Lean compiler output
// Module: Lean.Compiler.LCNF.PublicDeclsExt
// Imports: Lean.Environment
use crate::ffi::{lean_nat_sub, lean_string_dec_eq};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Prelude::l_List_lengthTR___redArg;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment,
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_Environment_header,
    l_Lean_registerEnvExtension___redArg, runtime_initialize_Lean_Environment,
};
pub static l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_isDeclPublic___closed__0_value: leanh::LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_isDeclPublic___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_isDeclPublic___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_isDeclPublic___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [95, 98, 111, 120, 101, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_isDeclPublic___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_isDeclPublic___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(
    mut v_newState_130_: *mut leanh::LeanObject,
    mut v_x_131_: *mut leanh::LeanObject,
    mut v_x_132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_137_: u8 = 0;
    let mut v_fst_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: u8 = 0;
    let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_143_: u8 = 0;
    let mut v_snd_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: u8 = 0;
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_158_: u8 = 0;
    let mut v_unused_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_132_) == 0 {
                    return v_x_131_;
                } else {
                    v_head_133_ = leanh::lean_ctor_get(v_x_132_, 0);
                    v_tail_134_ = leanh::lean_ctor_get(v_x_132_, 1);
                    v_isSharedCheck_162_ = (!leanh::lean_is_exclusive(v_x_132_)) as u8;
                    if v_isSharedCheck_162_ == 0 {
                        v___x_136_ = v_x_132_;
                        v_isShared_137_ = v_isSharedCheck_162_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_134_);
                        leanh::lean_inc(v_head_133_);
                        leanh::lean_dec(v_x_132_);
                        v___x_136_ = leanh::lean_box(0);
                        v_isShared_137_ = v_isSharedCheck_162_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_138_ = leanh::lean_ctor_get(v_x_131_, 0);
                v_snd_139_ = leanh::lean_ctor_get(v_x_131_, 1);
                v___x_140_ = l_Lean_NameSet_contains(v_snd_139_, v_head_133_);
                if v___x_140_ == 0 {
                    leanh::lean_inc(v_snd_139_);
                    leanh::lean_inc(v_fst_138_);
                    v_isSharedCheck_158_ = (!leanh::lean_is_exclusive(v_x_131_)) as u8;
                    if v_isSharedCheck_158_ == 0 {
                        v_unused_159_ = leanh::lean_ctor_get(v_x_131_, 1);
                        leanh::lean_dec(v_unused_159_);
                        v_unused_160_ = leanh::lean_ctor_get(v_x_131_, 0);
                        leanh::lean_dec(v_unused_160_);
                        v___x_142_ = v_x_131_;
                        v_isShared_143_ = v_isSharedCheck_158_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_131_);
                        v___x_142_ = leanh::lean_box(0);
                        v_isShared_143_ = v_isSharedCheck_158_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_136_);
                    leanh::lean_dec(v_head_133_);
                    v_x_132_ = v_tail_134_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_snd_144_ = leanh::lean_ctor_get(v_newState_130_, 1);
                leanh::lean_inc(v_head_133_);
                if v_isShared_137_ == 0 {
                    leanh::lean_ctor_set(v___x_136_, 1, v_fst_138_);
                    v___x_146_ = v___x_136_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_157_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_157_, 0, v_head_133_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_157_, 1, v_fst_138_);
                    v___x_146_ = v_reuseFailAlloc_157_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_147_ = l_Lean_NameSet_contains(v_snd_144_, v_head_133_);
                if v___x_147_ == 0 {
                    leanh::lean_dec(v_head_133_);
                    if v_isShared_143_ == 0 {
                        leanh::lean_ctor_set(v___x_142_, 0, v___x_146_);
                        v___x_149_ = v___x_142_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_151_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_146_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_151_, 1, v_snd_139_);
                        v___x_149_ = v_reuseFailAlloc_151_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_152_ = l_Lean_NameSet_insert(v_snd_139_, v_head_133_);
                    if v_isShared_143_ == 0 {
                        leanh::lean_ctor_set(v___x_142_, 1, v___x_152_);
                        leanh::lean_ctor_set(v___x_142_, 0, v___x_146_);
                        v___x_154_ = v___x_142_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_146_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_152_);
                        v___x_154_ = v_reuseFailAlloc_156_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v_x_131_ = v___x_149_;
                v_x_132_ = v_tail_134_;
                state = 0;
                continue;
            }
            5 => {
                v_x_131_ = v___x_154_;
                v_x_132_ = v_tail_134_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0___boxed(
    mut v_newState_163_: *mut leanh::LeanObject,
    mut v_x_164_: *mut leanh::LeanObject,
    mut v_x_165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_166_ = l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(
        v_newState_163_,
        v_x_164_,
        v_x_165_,
    );
    leanh::lean_dec_ref(v_newState_163_);
    return v_res_166_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0(
    mut v_oldState_169_: *mut leanh::LeanObject,
    mut v_newState_170_: *mut leanh::LeanObject,
    mut v_x_171_: *mut leanh::LeanObject,
    mut v_s_172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_173_ = leanh::lean_ctor_get(v_newState_170_, 0);
    v_fst_174_ = leanh::lean_ctor_get(v_oldState_169_, 0);
    v___x_175_ = l_List_lengthTR___redArg(v_fst_173_);
    v___x_176_ = l_List_lengthTR___redArg(v_fst_174_);
    v___x_177_ = lean_nat_sub(v___x_175_, v___x_176_);
    leanh::lean_dec(v___x_176_);
    leanh::lean_dec(v___x_175_);
    v___x_178_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0;
    leanh::lean_inc(v_fst_173_);
    v_newEntries_179_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        leanh::lean_box(0),
        v_fst_173_,
        v_fst_173_,
        v___x_177_,
        v___x_178_,
    );
    v___x_180_ = l_List_reverse___redArg(v_newEntries_179_);
    v___x_181_ = l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(
        v_newState_170_,
        v_s_172_,
        v___x_180_,
    );
    leanh::lean_dec_ref(v_newState_170_);
    return v___x_181_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___boxed(
    mut v_oldState_182_: *mut leanh::LeanObject,
    mut v_newState_183_: *mut leanh::LeanObject,
    mut v_x_184_: *mut leanh::LeanObject,
    mut v_s_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_186_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0(
        v_oldState_182_,
        v_newState_183_,
        v_x_184_,
        v_s_185_,
    );
    leanh::lean_dec(v_x_184_);
    leanh::lean_dec_ref(v_oldState_182_);
    return v_res_186_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(
    mut v___x_187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_189_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_189_, 0, v___x_187_);
    return v___x_189_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1___boxed(
    mut v___x_190_: *mut leanh::LeanObject,
    mut v___y_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_192_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(v___x_190_);
    return v_res_192_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_194_ = l_Lean_NameSet_empty;
    v___x_195_ = leanh::lean_box(0);
    v___x_196_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_196_, 0, v___x_195_);
    leanh::lean_ctor_set(v___x_196_, 1, v___x_194_);
    return v___x_196_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_197_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1_once),
        _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1,
    );
    v___f_198_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_198_, 0, v___x_197_);
    return v___f_198_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt() -> *mut leanh::LeanObject {
    let mut v___f_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_202_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2_once),
        _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2,
    );
    v___x_203_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3;
    v___x_204_ = leanh::lean_box(0);
    v___x_205_ = l_Lean_registerEnvExtension___redArg(v___f_202_, v___x_203_, v___x_204_);
    return v___x_205_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___boxed(
    mut v_a_206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_207_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
    return v_res_207_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_209_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
    return v___x_209_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2____boxed(
    mut v_a_210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_211_ = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
    return v_res_211_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isDeclPublic(
    mut v_env_216_: *mut leanh::LeanObject,
    mut v_declName_217_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: u8 = 0;
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_228_: u8 = 0;
    let mut v___x_229_: u8 = 0;
    let mut v_pre_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_227_ = l_Lean_Environment_header(v_env_216_);
                v_isModule_228_ = leanh::lean_ctor_get_uint8(
                    v___x_227_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                );
                leanh::lean_dec_ref(v___x_227_);
                if v_isModule_228_ == 0 {
                    leanh::lean_dec_ref(v_env_216_);
                    v___x_229_ = 1;
                    return v___x_229_;
                } else {
                    if leanh::lean_obj_tag(v_declName_217_) == 1 {
                        v_pre_230_ = leanh::lean_ctor_get(v_declName_217_, 0);
                        v_str_231_ = leanh::lean_ctor_get(v_declName_217_, 1);
                        v___x_232_ = l_Lean_Compiler_LCNF_isDeclPublic___closed__1;
                        v___x_233_ = lean_string_dec_eq(v_str_231_, v___x_232_);
                        if v___x_233_ == 0 {
                            v___y_219_ = v_declName_217_;
                            state = 1;
                            continue;
                        } else {
                            v___y_219_ = v_pre_230_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_219_ = v_declName_217_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_220_ = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
                v_asyncMode_221_ = leanh::lean_ctor_get(v___x_220_, 2);
                v___x_222_ = l_Lean_Compiler_LCNF_isDeclPublic___closed__0;
                v___x_223_ = leanh::lean_box(0);
                v___x_224_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_222_,
                        v___x_220_,
                        v_env_216_,
                        v_asyncMode_221_,
                        v___x_223_,
                    );
                v_snd_225_ = leanh::lean_ctor_get(v___x_224_, 1);
                leanh::lean_inc(v_snd_225_);
                leanh::lean_dec(v___x_224_);
                v___x_226_ = l_Lean_NameSet_contains(v_snd_225_, v___y_219_);
                leanh::lean_dec(v_snd_225_);
                return v___x_226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isDeclPublic___boxed(
    mut v_env_234_: *mut leanh::LeanObject,
    mut v_declName_235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_236_: u8 = 0;
    let mut v_r_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_234_, v_declName_235_);
    leanh::lean_dec(v_declName_235_);
    v_r_237_ = leanh::lean_box((v_res_236_) as usize);
    return v_r_237_;
}
pub unsafe fn l_Lean_Compiler_LCNF_setDeclPublic___lam__0(
    mut v_declName_238_: *mut leanh::LeanObject,
    mut v_s_239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_244_: u8 = 0;
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_240_ = leanh::lean_ctor_get(v_s_239_, 0);
                v_snd_241_ = leanh::lean_ctor_get(v_s_239_, 1);
                v_isSharedCheck_250_ = (!leanh::lean_is_exclusive(v_s_239_)) as u8;
                if v_isSharedCheck_250_ == 0 {
                    v___x_243_ = v_s_239_;
                    v_isShared_244_ = v_isSharedCheck_250_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_241_);
                    leanh::lean_inc(v_fst_240_);
                    leanh::lean_dec(v_s_239_);
                    v___x_243_ = leanh::lean_box(0);
                    v_isShared_244_ = v_isSharedCheck_250_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_declName_238_);
                v___x_245_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_245_, 0, v_declName_238_);
                leanh::lean_ctor_set(v___x_245_, 1, v_fst_240_);
                v___x_246_ = l_Lean_NameSet_insert(v_snd_241_, v_declName_238_);
                if v_isShared_244_ == 0 {
                    leanh::lean_ctor_set(v___x_243_, 1, v___x_246_);
                    leanh::lean_ctor_set(v___x_243_, 0, v___x_245_);
                    v___x_248_ = v___x_243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_249_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_245_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_246_);
                    v___x_248_ = v_reuseFailAlloc_249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_248_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_setDeclPublic(
    mut v_env_251_: *mut leanh::LeanObject,
    mut v_declName_252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_253_: u8 = 0;
    leanh::lean_inc_ref(v_env_251_);
    v___x_253_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_251_, v_declName_252_);
    if v___x_253_ == 0 {
        let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_254_ =
            l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
        v_asyncMode_255_ = leanh::lean_ctor_get(v___x_254_, 2);
        v___f_256_ = leanh::lean_alloc_closure(
            l_Lean_Compiler_LCNF_setDeclPublic___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_256_, 0, v_declName_252_);
        v___x_257_ = leanh::lean_box(0);
        v___x_258_ = l_Lean_EnvExtension_modifyState___redArg(
            v___x_254_,
            v_env_251_,
            v___f_256_,
            v_asyncMode_255_,
            v___x_257_,
        );
        return v___x_258_;
    } else {
        leanh::lean_dec(v_declName_252_);
        return v_env_251_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt,
    );
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PublicDeclsExt(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_PublicDeclsExt(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
}
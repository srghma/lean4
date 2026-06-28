// Lean compiler output
// Module: Lean.Compiler.LCNF.PublicDeclsExt
// Imports: Lean.Environment
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_sub, lean_string_dec_eq,
};
pub static l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_isDeclPublic___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_isDeclPublic___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_isDeclPublic___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_isDeclPublic___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_isDeclPublic___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_isDeclPublic___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(
    mut v_newState_130_: *mut crate::leanh::LeanObject,
    mut v_x_131_: *mut crate::leanh::LeanObject,
    mut v_x_132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_137_: u8 = 0;
    let mut v_fst_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: u8 = 0;
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_143_: u8 = 0;
    let mut v_snd_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: u8 = 0;
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_158_: u8 = 0;
    let mut v_unused_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_132_) == 0 {
                    return v_x_131_;
                } else {
                    v_head_133_ = crate::leanh::lean_ctor_get(v_x_132_, 0);
                    v_tail_134_ = crate::leanh::lean_ctor_get(v_x_132_, 1);
                    v_isSharedCheck_162_ = (!crate::leanh::lean_is_exclusive(v_x_132_)) as u8;
                    if v_isSharedCheck_162_ == 0 {
                        v___x_136_ = v_x_132_;
                        v_isShared_137_ = v_isSharedCheck_162_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_134_);
                        crate::leanh::lean_inc(v_head_133_);
                        crate::leanh::lean_dec(v_x_132_);
                        v___x_136_ = crate::leanh::lean_box(0);
                        v_isShared_137_ = v_isSharedCheck_162_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_138_ = crate::leanh::lean_ctor_get(v_x_131_, 0);
                v_snd_139_ = crate::leanh::lean_ctor_get(v_x_131_, 1);
                v___x_140_ = l_Lean_NameSet_contains(v_snd_139_, v_head_133_);
                if v___x_140_ == 0 {
                    crate::leanh::lean_inc(v_snd_139_);
                    crate::leanh::lean_inc(v_fst_138_);
                    v_isSharedCheck_158_ = (!crate::leanh::lean_is_exclusive(v_x_131_)) as u8;
                    if v_isSharedCheck_158_ == 0 {
                        v_unused_159_ = crate::leanh::lean_ctor_get(v_x_131_, 1);
                        crate::leanh::lean_dec(v_unused_159_);
                        v_unused_160_ = crate::leanh::lean_ctor_get(v_x_131_, 0);
                        crate::leanh::lean_dec(v_unused_160_);
                        v___x_142_ = v_x_131_;
                        v_isShared_143_ = v_isSharedCheck_158_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_131_);
                        v___x_142_ = crate::leanh::lean_box(0);
                        v_isShared_143_ = v_isSharedCheck_158_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_136_);
                    crate::leanh::lean_dec(v_head_133_);
                    v_x_132_ = v_tail_134_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_snd_144_ = crate::leanh::lean_ctor_get(v_newState_130_, 1);
                crate::leanh::lean_inc(v_head_133_);
                if v_isShared_137_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_136_, 1, v_fst_138_);
                    v___x_146_ = v___x_136_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_157_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_157_, 0, v_head_133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_157_, 1, v_fst_138_);
                    v___x_146_ = v_reuseFailAlloc_157_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_147_ = l_Lean_NameSet_contains(v_snd_144_, v_head_133_);
                if v___x_147_ == 0 {
                    crate::leanh::lean_dec(v_head_133_);
                    if v_isShared_143_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_142_, 0, v___x_146_);
                        v___x_149_ = v___x_142_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_151_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_146_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_151_, 1, v_snd_139_);
                        v___x_149_ = v_reuseFailAlloc_151_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_152_ = l_Lean_NameSet_insert(v_snd_139_, v_head_133_);
                    if v_isShared_143_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_142_, 1, v___x_152_);
                        crate::leanh::lean_ctor_set(v___x_142_, 0, v___x_146_);
                        v___x_154_ = v___x_142_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_156_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_146_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_152_);
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
    mut v_newState_163_: *mut crate::leanh::LeanObject,
    mut v_x_164_: *mut crate::leanh::LeanObject,
    mut v_x_165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_166_ = l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(
        v_newState_163_,
        v_x_164_,
        v_x_165_,
    );
    crate::leanh::lean_dec_ref(v_newState_163_);
    return v_res_166_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0(
    mut v_oldState_169_: *mut crate::leanh::LeanObject,
    mut v_newState_170_: *mut crate::leanh::LeanObject,
    mut v_x_171_: *mut crate::leanh::LeanObject,
    mut v_s_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_173_ = crate::leanh::lean_ctor_get(v_newState_170_, 0);
    v_fst_174_ = crate::leanh::lean_ctor_get(v_oldState_169_, 0);
    v___x_175_ = l_List_lengthTR___redArg(v_fst_173_);
    v___x_176_ = l_List_lengthTR___redArg(v_fst_174_);
    v___x_177_ = lean_nat_sub(v___x_175_, v___x_176_);
    crate::leanh::lean_dec(v___x_176_);
    crate::leanh::lean_dec(v___x_175_);
    v___x_178_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0;
    crate::leanh::lean_inc(v_fst_173_);
    v_newEntries_179_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        crate::leanh::lean_box(0),
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
    crate::leanh::lean_dec_ref(v_newState_170_);
    return v___x_181_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___boxed(
    mut v_oldState_182_: *mut crate::leanh::LeanObject,
    mut v_newState_183_: *mut crate::leanh::LeanObject,
    mut v_x_184_: *mut crate::leanh::LeanObject,
    mut v_s_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_186_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0(
        v_oldState_182_,
        v_newState_183_,
        v_x_184_,
        v_s_185_,
    );
    crate::leanh::lean_dec(v_x_184_);
    crate::leanh::lean_dec_ref(v_oldState_182_);
    return v_res_186_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(
    mut v___x_187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_189_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_189_, 0, v___x_187_);
    return v___x_189_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1___boxed(
    mut v___x_190_: *mut crate::leanh::LeanObject,
    mut v___y_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_192_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(v___x_190_);
    return v_res_192_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_194_ = l_Lean_NameSet_empty;
    v___x_195_ = crate::leanh::lean_box(0);
    v___x_196_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_196_, 0, v___x_195_);
    crate::leanh::lean_ctor_set(v___x_196_, 1, v___x_194_);
    return v___x_196_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_197_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1_once),
        _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1,
    );
    v___f_198_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_198_, 0, v___x_197_);
    return v___f_198_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt() -> *mut crate::leanh::LeanObject {
    let mut v___f_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_202_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2_once),
        _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2,
    );
    v___x_203_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3;
    v___x_204_ = crate::leanh::lean_box(0);
    v___x_205_ = l_Lean_registerEnvExtension___redArg(v___f_202_, v___x_203_, v___x_204_);
    return v___x_205_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___boxed(
    mut v_a_206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_207_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
    return v_res_207_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_209_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
    return v___x_209_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2____boxed(
    mut v_a_210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_211_ = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
    return v_res_211_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isDeclPublic(
    mut v_env_216_: *mut crate::leanh::LeanObject,
    mut v_declName_217_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: u8 = 0;
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_228_: u8 = 0;
    let mut v___x_229_: u8 = 0;
    let mut v_pre_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_227_ = l_Lean_Environment_header(v_env_216_);
                v_isModule_228_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_227_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
                );
                crate::leanh::lean_dec_ref(v___x_227_);
                if v_isModule_228_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_216_);
                    v___x_229_ = 1;
                    return v___x_229_;
                } else {
                    if crate::leanh::lean_obj_tag(v_declName_217_) == 1 {
                        v_pre_230_ = crate::leanh::lean_ctor_get(v_declName_217_, 0);
                        v_str_231_ = crate::leanh::lean_ctor_get(v_declName_217_, 1);
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
                v_asyncMode_221_ = crate::leanh::lean_ctor_get(v___x_220_, 2);
                v___x_222_ = l_Lean_Compiler_LCNF_isDeclPublic___closed__0;
                v___x_223_ = crate::leanh::lean_box(0);
                v___x_224_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_222_,
                        v___x_220_,
                        v_env_216_,
                        v_asyncMode_221_,
                        v___x_223_,
                    );
                v_snd_225_ = crate::leanh::lean_ctor_get(v___x_224_, 1);
                crate::leanh::lean_inc(v_snd_225_);
                crate::leanh::lean_dec(v___x_224_);
                v___x_226_ = l_Lean_NameSet_contains(v_snd_225_, v___y_219_);
                crate::leanh::lean_dec(v_snd_225_);
                return v___x_226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isDeclPublic___boxed(
    mut v_env_234_: *mut crate::leanh::LeanObject,
    mut v_declName_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_236_: u8 = 0;
    let mut v_r_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_234_, v_declName_235_);
    crate::leanh::lean_dec(v_declName_235_);
    v_r_237_ = crate::leanh::lean_box((v_res_236_) as usize);
    return v_r_237_;
}
pub unsafe fn l_Lean_Compiler_LCNF_setDeclPublic___lam__0(
    mut v_declName_238_: *mut crate::leanh::LeanObject,
    mut v_s_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_244_: u8 = 0;
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_240_ = crate::leanh::lean_ctor_get(v_s_239_, 0);
                v_snd_241_ = crate::leanh::lean_ctor_get(v_s_239_, 1);
                v_isSharedCheck_250_ = (!crate::leanh::lean_is_exclusive(v_s_239_)) as u8;
                if v_isSharedCheck_250_ == 0 {
                    v___x_243_ = v_s_239_;
                    v_isShared_244_ = v_isSharedCheck_250_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_241_);
                    crate::leanh::lean_inc(v_fst_240_);
                    crate::leanh::lean_dec(v_s_239_);
                    v___x_243_ = crate::leanh::lean_box(0);
                    v_isShared_244_ = v_isSharedCheck_250_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_declName_238_);
                v___x_245_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_245_, 0, v_declName_238_);
                crate::leanh::lean_ctor_set(v___x_245_, 1, v_fst_240_);
                v___x_246_ = l_Lean_NameSet_insert(v_snd_241_, v_declName_238_);
                if v_isShared_244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_243_, 1, v___x_246_);
                    crate::leanh::lean_ctor_set(v___x_243_, 0, v___x_245_);
                    v___x_248_ = v___x_243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_249_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_245_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_246_);
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
    mut v_env_251_: *mut crate::leanh::LeanObject,
    mut v_declName_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_253_: u8 = 0;
    crate::leanh::lean_inc_ref(v_env_251_);
    v___x_253_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_251_, v_declName_252_);
    if v___x_253_ == 0 {
        let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_254_ =
            l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
        v_asyncMode_255_ = crate::leanh::lean_ctor_get(v___x_254_, 2);
        v___f_256_ = crate::leanh::lean_alloc_closure(
            l_Lean_Compiler_LCNF_setDeclPublic___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_256_, 0, v_declName_252_);
        v___x_257_ = crate::leanh::lean_box(0);
        v___x_258_ = l_Lean_EnvExtension_modifyState___redArg(
            v___x_254_,
            v_env_251_,
            v___f_256_,
            v_asyncMode_255_,
            v___x_257_,
        );
        return v___x_258_;
    } else {
        crate::leanh::lean_dec(v_declName_252_);
        return v_env_251_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt,
    );
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PublicDeclsExt(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_PublicDeclsExt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
}

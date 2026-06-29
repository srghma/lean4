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
use crate::ffi::{lean_array_size, lean_mk_array};
pub static l_Std_Sat_AIG_relabel___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Sat_AIG_relabel___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Sat_AIG_relabel___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Sat_AIG_relabel___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Sat_AIG_relabel___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Sat_AIG_relabel___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Sat_AIG_relabel___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Sat_AIG_relabel___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Sat_AIG_relabel___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_relabel___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Sat_AIG_relabel___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Sat_AIG_relabel___redArg___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_relabel___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Sat_AIG_Decl_relabel___redArg(
    mut v_r_153_: *mut crate::leanh::LeanObject,
    mut v_decl_154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_159_: u8 = 0;
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_164_: u8 = 0;
    let mut v_l_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_169_: u8 = 0;
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_decl_154_) {
                0 => {
                    crate::leanh::lean_dec(v_r_153_);
                    v___x_155_ = crate::leanh::lean_box(0);
                    return v___x_155_;
                }
                1 => {
                    v_idx_156_ = crate::leanh::lean_ctor_get(v_decl_154_, 0);
                    v_isSharedCheck_164_ = (!crate::leanh::lean_is_exclusive(v_decl_154_)) as u8;
                    if v_isSharedCheck_164_ == 0 {
                        v___x_158_ = v_decl_154_;
                        v_isShared_159_ = v_isSharedCheck_164_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_156_);
                        crate::leanh::lean_dec(v_decl_154_);
                        v___x_158_ = crate::leanh::lean_box(0);
                        v_isShared_159_ = v_isSharedCheck_164_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_r_153_);
                    v_l_165_ = crate::leanh::lean_ctor_get(v_decl_154_, 0);
                    v_r_166_ = crate::leanh::lean_ctor_get(v_decl_154_, 1);
                    v_isSharedCheck_173_ = (!crate::leanh::lean_is_exclusive(v_decl_154_)) as u8;
                    if v_isSharedCheck_173_ == 0 {
                        v___x_168_ = v_decl_154_;
                        v_isShared_169_ = v_isSharedCheck_173_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_166_);
                        crate::leanh::lean_inc(v_l_165_);
                        crate::leanh::lean_dec(v_decl_154_);
                        v___x_168_ = crate::leanh::lean_box(0);
                        v_isShared_169_ = v_isSharedCheck_173_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_160_ = crate::leanh::lean_apply_1(v_r_153_, v_idx_156_);
                if v_isShared_159_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_158_, 0, v___x_160_);
                    v___x_162_ = v___x_158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
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
                    v_reuseFailAlloc_172_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_172_, 0, v_l_165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_172_, 1, v_r_166_);
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
    mut v_00_u03b1_174_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_175_: *mut crate::leanh::LeanObject,
    mut v_r_176_: *mut crate::leanh::LeanObject,
    mut v_decl_177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_178_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_176_, v_decl_177_);
    return v___x_178_;
}
pub unsafe fn l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___redArg(
    mut v_decl_179_: *mut crate::leanh::LeanObject,
    mut v_h__1_180_: *mut crate::leanh::LeanObject,
    mut v_h__2_181_: *mut crate::leanh::LeanObject,
    mut v_h__3_182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_decl_179_) {
        0 => {
            let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_182_);
            crate::leanh::lean_dec(v_h__2_181_);
            v___x_183_ = crate::leanh::lean_box(0);
            v___x_184_ = crate::leanh::lean_apply_1(v_h__1_180_, v___x_183_);
            return v___x_184_;
        }
        1 => {
            let mut v_idx_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_182_);
            crate::leanh::lean_dec(v_h__1_180_);
            v_idx_185_ = crate::leanh::lean_ctor_get(v_decl_179_, 0);
            crate::leanh::lean_inc(v_idx_185_);
            crate::leanh::lean_dec_ref_known(v_decl_179_, 1);
            v___x_186_ = crate::leanh::lean_apply_1(v_h__2_181_, v_idx_185_);
            return v___x_186_;
        }
        _ => {
            let mut v_l_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_181_);
            crate::leanh::lean_dec(v_h__1_180_);
            v_l_187_ = crate::leanh::lean_ctor_get(v_decl_179_, 0);
            crate::leanh::lean_inc(v_l_187_);
            v_r_188_ = crate::leanh::lean_ctor_get(v_decl_179_, 1);
            crate::leanh::lean_inc(v_r_188_);
            crate::leanh::lean_dec_ref_known(v_decl_179_, 2);
            v___x_189_ = crate::leanh::lean_apply_2(v_h__3_182_, v_l_187_, v_r_188_);
            return v___x_189_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter(
    mut v_00_u03b1_190_: *mut crate::leanh::LeanObject,
    mut v_motive_191_: *mut crate::leanh::LeanObject,
    mut v_decl_192_: *mut crate::leanh::LeanObject,
    mut v_h__1_193_: *mut crate::leanh::LeanObject,
    mut v_h__2_194_: *mut crate::leanh::LeanObject,
    mut v_h__3_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_decl_192_) {
        0 => {
            let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_195_);
            crate::leanh::lean_dec(v_h__2_194_);
            v___x_196_ = crate::leanh::lean_box(0);
            v___x_197_ = crate::leanh::lean_apply_1(v_h__1_193_, v___x_196_);
            return v___x_197_;
        }
        1 => {
            let mut v_idx_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_195_);
            crate::leanh::lean_dec(v_h__1_193_);
            v_idx_198_ = crate::leanh::lean_ctor_get(v_decl_192_, 0);
            crate::leanh::lean_inc(v_idx_198_);
            crate::leanh::lean_dec_ref_known(v_decl_192_, 1);
            v___x_199_ = crate::leanh::lean_apply_1(v_h__2_194_, v_idx_198_);
            return v___x_199_;
        }
        _ => {
            let mut v_l_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_194_);
            crate::leanh::lean_dec(v_h__1_193_);
            v_l_200_ = crate::leanh::lean_ctor_get(v_decl_192_, 0);
            crate::leanh::lean_inc(v_l_200_);
            v_r_201_ = crate::leanh::lean_ctor_get(v_decl_192_, 1);
            crate::leanh::lean_inc(v_r_201_);
            crate::leanh::lean_dec_ref_known(v_decl_192_, 2);
            v___x_202_ = crate::leanh::lean_apply_2(v_h__3_195_, v_l_200_, v_r_201_);
            return v___x_202_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_relabel___redArg___lam__0(
    mut v_r_203_: *mut crate::leanh::LeanObject,
    mut v_x_204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_205_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_203_, v_x_204_);
    return v___x_205_;
}
pub unsafe fn _init_l_Std_Sat_AIG_relabel___redArg___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_225_ = crate::leanh::lean_box(0);
    v___x_226_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_227_ = lean_mk_array(v___x_226_, v___x_225_);
    return v___x_227_;
}
pub unsafe fn _init_l_Std_Sat_AIG_relabel___redArg___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_228_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___redArg___closed__10_once),
        _init_l_Std_Sat_AIG_relabel___redArg___closed__10,
    );
    v___x_229_ = crate::leanh::lean_unsigned_to_nat(0);
    v_cache_230_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_cache_230_, 0, v___x_229_);
    crate::leanh::lean_ctor_set(v_cache_230_, 1, v___x_228_);
    return v_cache_230_;
}
pub unsafe fn l_Std_Sat_AIG_relabel___redArg(
    mut v_r_231_: *mut crate::leanh::LeanObject,
    mut v_aig_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_236_: u8 = 0;
    let mut v___f_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_239_: usize = 0;
    let mut v___x_240_: usize = 0;
    let mut v_decls_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_246_: u8 = 0;
    let mut v_unused_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_233_ = crate::leanh::lean_ctor_get(v_aig_232_, 0);
                v_isSharedCheck_246_ = (!crate::leanh::lean_is_exclusive(v_aig_232_)) as u8;
                if v_isSharedCheck_246_ == 0 {
                    v_unused_247_ = crate::leanh::lean_ctor_get(v_aig_232_, 1);
                    crate::leanh::lean_dec(v_unused_247_);
                    v___x_235_ = v_aig_232_;
                    v_isShared_236_ = v_isSharedCheck_246_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_decls_233_);
                    crate::leanh::lean_dec(v_aig_232_);
                    v___x_235_ = crate::leanh::lean_box(0);
                    v_isShared_236_ = v_isSharedCheck_246_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_237_ = crate::leanh::lean_alloc_closure(
                    l_Std_Sat_AIG_relabel___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_237_, 0, v_r_231_);
                v___x_238_ = l_Std_Sat_AIG_relabel___redArg___closed__9;
                v_sz_239_ = lean_array_size(v_decls_233_);
                v___x_240_ = 0usize;
                v_decls_241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_238_,
                    v___f_237_,
                    v_sz_239_,
                    v___x_240_,
                    v_decls_233_,
                );
                v_cache_242_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___redArg___closed__11),
                    core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___redArg___closed__11_once),
                    _init_l_Std_Sat_AIG_relabel___redArg___closed__11,
                );
                if v_isShared_236_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_235_, 1, v_cache_242_);
                    crate::leanh::lean_ctor_set(v___x_235_, 0, v_decls_241_);
                    v___x_244_ = v___x_235_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_245_, 0, v_decls_241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_245_, 1, v_cache_242_);
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
    mut v_00_u03b1_248_: *mut crate::leanh::LeanObject,
    mut v_inst_249_: *mut crate::leanh::LeanObject,
    mut v_inst_250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_251_: *mut crate::leanh::LeanObject,
    mut v_inst_252_: *mut crate::leanh::LeanObject,
    mut v_inst_253_: *mut crate::leanh::LeanObject,
    mut v_r_254_: *mut crate::leanh::LeanObject,
    mut v_aig_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_256_ = l_Std_Sat_AIG_relabel___redArg(v_r_254_, v_aig_255_);
    return v___x_256_;
}
pub unsafe fn l_Std_Sat_AIG_relabel___boxed(
    mut v_00_u03b1_257_: *mut crate::leanh::LeanObject,
    mut v_inst_258_: *mut crate::leanh::LeanObject,
    mut v_inst_259_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_260_: *mut crate::leanh::LeanObject,
    mut v_inst_261_: *mut crate::leanh::LeanObject,
    mut v_inst_262_: *mut crate::leanh::LeanObject,
    mut v_r_263_: *mut crate::leanh::LeanObject,
    mut v_aig_264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_262_);
    crate::leanh::lean_dec_ref(v_inst_261_);
    crate::leanh::lean_dec_ref(v_inst_259_);
    crate::leanh::lean_dec_ref(v_inst_258_);
    return v_res_265_;
}
pub unsafe fn l_Std_Sat_AIG_Entrypoint_relabel___redArg(
    mut v_r_266_: *mut crate::leanh::LeanObject,
    mut v_entry_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_272_: u8 = 0;
    let mut v_gate_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_274_: u8 = 0;
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_277_: u8 = 0;
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_285_: u8 = 0;
    let mut v_isSharedCheck_286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_268_ = crate::leanh::lean_ctor_get(v_entry_267_, 1);
                v_aig_269_ = crate::leanh::lean_ctor_get(v_entry_267_, 0);
                v_isSharedCheck_286_ = (!crate::leanh::lean_is_exclusive(v_entry_267_)) as u8;
                if v_isSharedCheck_286_ == 0 {
                    v___x_271_ = v_entry_267_;
                    v_isShared_272_ = v_isSharedCheck_286_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_268_);
                    crate::leanh::lean_inc(v_aig_269_);
                    crate::leanh::lean_dec(v_entry_267_);
                    v___x_271_ = crate::leanh::lean_box(0);
                    v_isShared_272_ = v_isSharedCheck_286_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_273_ = crate::leanh::lean_ctor_get(v_ref_268_, 0);
                v_invert_274_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_268_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_285_ = (!crate::leanh::lean_is_exclusive(v_ref_268_)) as u8;
                if v_isSharedCheck_285_ == 0 {
                    v___x_276_ = v_ref_268_;
                    v_isShared_277_ = v_isSharedCheck_285_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_273_);
                    crate::leanh::lean_dec(v_ref_268_);
                    v___x_276_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_284_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_284_, 0, v_gate_273_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_274_,
                    );
                    v___x_280_ = v_reuseFailAlloc_284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_272_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_271_, 1, v___x_280_);
                    crate::leanh::lean_ctor_set(v___x_271_, 0, v___x_278_);
                    v___x_282_ = v___x_271_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_283_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_280_);
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
    mut v_00_u03b1_287_: *mut crate::leanh::LeanObject,
    mut v_inst_288_: *mut crate::leanh::LeanObject,
    mut v_inst_289_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_290_: *mut crate::leanh::LeanObject,
    mut v_inst_291_: *mut crate::leanh::LeanObject,
    mut v_inst_292_: *mut crate::leanh::LeanObject,
    mut v_r_293_: *mut crate::leanh::LeanObject,
    mut v_entry_294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = l_Std_Sat_AIG_Entrypoint_relabel___redArg(v_r_293_, v_entry_294_);
    return v___x_295_;
}
pub unsafe fn l_Std_Sat_AIG_Entrypoint_relabel___boxed(
    mut v_00_u03b1_296_: *mut crate::leanh::LeanObject,
    mut v_inst_297_: *mut crate::leanh::LeanObject,
    mut v_inst_298_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_299_: *mut crate::leanh::LeanObject,
    mut v_inst_300_: *mut crate::leanh::LeanObject,
    mut v_inst_301_: *mut crate::leanh::LeanObject,
    mut v_r_302_: *mut crate::leanh::LeanObject,
    mut v_entry_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_301_);
    crate::leanh::lean_dec_ref(v_inst_300_);
    crate::leanh::lean_dec_ref(v_inst_298_);
    crate::leanh::lean_dec_ref(v_inst_297_);
    return v_res_304_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_Relabel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_Relabel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_Relabel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_Relabel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_Relabel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_Relabel(builtin);
}

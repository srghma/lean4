// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ProofUtil
// Imports: Lean.Meta.Tactic.Grind.Types
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_expr_abstract,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_reverse___redArg,
};
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Lean::Expr::l_Lean_Expr_letE___override;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_foldlM___redArg;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value: leanh::LeanCtorObject<
    5,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value:
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
    m_fun: l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__12_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(
    mut v_x_138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_139_ = leanh::lean_ctor_get(v_x_138_, 1);
    leanh::lean_inc(v_snd_139_);
    return v_snd_139_;
}
pub unsafe fn l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0___boxed(
    mut v_x_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_141_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__0(v_x_140_);
    leanh::lean_dec_ref(v_x_140_);
    return v_res_141_;
}
pub unsafe fn l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(
    mut v_varPrefix_142_: *mut leanh::LeanObject,
    mut v_toExpr_143_: *mut leanh::LeanObject,
    mut v_varType_144_: *mut leanh::LeanObject,
    mut v___x_145_: u8,
    mut v_a_146_: *mut leanh::LeanObject,
    mut v_x_147_: *mut leanh::LeanObject,
    mut v___y_148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_154_: u8 = 0;
    let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_149_ = leanh::lean_ctor_get(v_a_146_, 0);
                leanh::lean_inc(v_fst_149_);
                leanh::lean_dec_ref(v_a_146_);
                v_fst_150_ = leanh::lean_ctor_get(v___y_148_, 0);
                v_snd_151_ = leanh::lean_ctor_get(v___y_148_, 1);
                v_isSharedCheck_164_ = (!leanh::lean_is_exclusive(v___y_148_)) as u8;
                if v_isSharedCheck_164_ == 0 {
                    v___x_153_ = v___y_148_;
                    v_isShared_154_ = v_isSharedCheck_164_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_151_);
                    leanh::lean_inc(v_fst_150_);
                    leanh::lean_dec(v___y_148_);
                    v___x_153_ = leanh::lean_box(0);
                    v_isShared_154_ = v_isSharedCheck_164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_snd_151_);
                v___x_155_ = lean_name_append_index_after(v_varPrefix_142_, v_snd_151_);
                v___x_156_ = leanh::lean_apply_1(v_toExpr_143_, v_fst_149_);
                v___x_157_ = l_Lean_Expr_letE___override(
                    v___x_155_,
                    v_varType_144_,
                    v___x_156_,
                    v_fst_150_,
                    v___x_145_,
                );
                v___x_158_ = leanh::lean_unsigned_to_nat(1);
                v___x_159_ = lean_nat_sub(v_snd_151_, v___x_158_);
                leanh::lean_dec(v_snd_151_);
                if v_isShared_154_ == 0 {
                    leanh::lean_ctor_set(v___x_153_, 1, v___x_159_);
                    leanh::lean_ctor_set(v___x_153_, 0, v___x_157_);
                    v___x_161_ = v___x_153_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_163_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_159_);
                    v___x_161_ = v_reuseFailAlloc_163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_162_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_162_, 0, v___x_161_);
                return v___x_162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed(
    mut v_varPrefix_165_: *mut leanh::LeanObject,
    mut v_toExpr_166_: *mut leanh::LeanObject,
    mut v_varType_167_: *mut leanh::LeanObject,
    mut v___x_168_: *mut leanh::LeanObject,
    mut v_a_169_: *mut leanh::LeanObject,
    mut v_x_170_: *mut leanh::LeanObject,
    mut v___y_171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_503__boxed_172_: u8 = 0;
    let mut v_res_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_503__boxed_172_ = (leanh::lean_unbox(v___x_168_) as u8);
    v_res_173_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1(
        v_varPrefix_165_,
        v_toExpr_166_,
        v_varType_167_,
        v___x_503__boxed_172_,
        v_a_169_,
        v_x_170_,
        v___y_171_,
    );
    return v_res_173_;
}
pub unsafe fn l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__2(
    mut v_x1_174_: *mut leanh::LeanObject,
    mut v_x2_175_: *mut leanh::LeanObject,
    mut v_x3_176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_177_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_177_, 0, v_x2_175_);
    leanh::lean_ctor_set(v___x_177_, 1, v_x3_176_);
    v___x_178_ = lean_array_push(v_x1_174_, v___x_177_);
    return v___x_178_;
}
pub unsafe fn l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__3(
    mut v___x_179_: *mut leanh::LeanObject,
    mut v___f_180_: *mut leanh::LeanObject,
    mut v_acc_181_: *mut leanh::LeanObject,
    mut v_l_182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_183_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_179_, v___f_180_, v_acc_181_, v_l_182_,
    );
    return v___x_183_;
}
pub unsafe fn l_Lean_Meta_Grind_mkLetOfMap___redArg(
    mut v_m_208_: *mut leanh::LeanObject,
    mut v_e_209_: *mut leanh::LeanObject,
    mut v_varPrefix_210_: *mut leanh::LeanObject,
    mut v_varType_211_: *mut leanh::LeanObject,
    mut v_toExpr_212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_217_: u8 = 0;
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: u8 = 0;
    let mut v___f_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_226_: usize = 0;
    let mut v___x_227_: usize = 0;
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_234_: usize = 0;
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: u8 = 0;
    let mut v___f_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: u8 = 0;
    let mut v___x_244_: usize = 0;
    let mut v___x_245_: usize = 0;
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: usize = 0;
    let mut v___x_248_: usize = 0;
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_213_ = leanh::lean_ctor_get(v_m_208_, 0);
                v_buckets_214_ = leanh::lean_ctor_get(v_m_208_, 1);
                v_isSharedCheck_250_ = (!leanh::lean_is_exclusive(v_m_208_)) as u8;
                if v_isSharedCheck_250_ == 0 {
                    v___x_216_ = v_m_208_;
                    v_isShared_217_ = v_isSharedCheck_250_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_214_);
                    leanh::lean_inc(v_size_213_);
                    leanh::lean_dec(v_m_208_);
                    v___x_216_ = leanh::lean_box(0);
                    v_isShared_217_ = v_isSharedCheck_250_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_218_ = leanh::lean_unsigned_to_nat(0);
                v___x_219_ = lean_nat_dec_eq(v_size_213_, v___x_218_);
                if v___x_219_ == 0 {
                    v___f_220_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__0;
                    v___x_221_ = leanh::lean_box((v___x_219_) as usize);
                    v___f_222_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_mkLetOfMap___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        7,
                        4,
                    );
                    leanh::lean_closure_set(v___f_222_, 0, v_varPrefix_210_);
                    leanh::lean_closure_set(v___f_222_, 1, v_toExpr_212_);
                    leanh::lean_closure_set(v___f_222_, 2, v_varType_211_);
                    leanh::lean_closure_set(v___f_222_, 3, v___x_221_);
                    v___x_238_ = lean_mk_empty_array_with_capacity(v_size_213_);
                    leanh::lean_dec(v_size_213_);
                    v___x_239_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10;
                    v___x_240_ = lean_array_get_size(v_buckets_214_);
                    v___x_241_ = lean_nat_dec_lt(v___x_218_, v___x_240_);
                    if v___x_241_ == 0 {
                        leanh::lean_dec_ref(v_buckets_214_);
                        v___y_224_ = v___x_238_;
                        state = 2;
                        continue;
                    } else {
                        v___f_242_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__12;
                        v___x_243_ = lean_nat_dec_le(v___x_240_, v___x_240_);
                        if v___x_243_ == 0 {
                            if v___x_241_ == 0 {
                                leanh::lean_dec_ref(v_buckets_214_);
                                v___y_224_ = v___x_238_;
                                state = 2;
                                continue;
                            } else {
                                v___x_244_ = 0usize;
                                v___x_245_ = lean_usize_of_nat(v___x_240_);
                                v___x_246_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_239_,
                                        v___f_242_,
                                        v_buckets_214_,
                                        v___x_244_,
                                        v___x_245_,
                                        v___x_238_,
                                    );
                                v___y_224_ = v___x_246_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_247_ = 0usize;
                            v___x_248_ = lean_usize_of_nat(v___x_240_);
                            v___x_249_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_239_,
                                    v___f_242_,
                                    v_buckets_214_,
                                    v___x_247_,
                                    v___x_248_,
                                    v___x_238_,
                                );
                            v___y_224_ = v___x_249_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_216_);
                    leanh::lean_dec_ref(v_buckets_214_);
                    leanh::lean_dec(v_size_213_);
                    leanh::lean_dec_ref(v_toExpr_212_);
                    leanh::lean_dec_ref(v_varType_211_);
                    leanh::lean_dec(v_varPrefix_210_);
                    leanh::lean_inc_ref(v_e_209_);
                    return v_e_209_;
                }
            }
            2 => {
                v___x_225_ = l_Lean_Meta_Grind_mkLetOfMap___redArg___closed__10;
                v_sz_226_ = lean_array_size(v___y_224_);
                v___x_227_ = 0usize;
                leanh::lean_inc_ref(v___y_224_);
                v___x_228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_225_,
                    v___f_220_,
                    v_sz_226_,
                    v___x_227_,
                    v___y_224_,
                );
                v_e_229_ = lean_expr_abstract(v_e_209_, v___x_228_);
                leanh::lean_dec(v___x_228_);
                v_i_230_ = lean_array_get_size(v___y_224_);
                v___x_231_ = l_Array_reverse___redArg(v___y_224_);
                if v_isShared_217_ == 0 {
                    leanh::lean_ctor_set(v___x_216_, 1, v_i_230_);
                    leanh::lean_ctor_set(v___x_216_, 0, v_e_229_);
                    v___x_233_ = v___x_216_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_237_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_237_, 0, v_e_229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_237_, 1, v_i_230_);
                    v___x_233_ = v_reuseFailAlloc_237_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_sz_234_ = lean_array_size(v___x_231_);
                v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_225_,
                    v___x_231_,
                    v___f_222_,
                    v_sz_234_,
                    v___x_227_,
                    v___x_233_,
                );
                v_fst_236_ = leanh::lean_ctor_get(v___x_235_, 0);
                leanh::lean_inc(v_fst_236_);
                leanh::lean_dec(v___x_235_);
                return v_fst_236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkLetOfMap___redArg___boxed(
    mut v_m_251_: *mut leanh::LeanObject,
    mut v_e_252_: *mut leanh::LeanObject,
    mut v_varPrefix_253_: *mut leanh::LeanObject,
    mut v_varType_254_: *mut leanh::LeanObject,
    mut v_toExpr_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_256_ = l_Lean_Meta_Grind_mkLetOfMap___redArg(
        v_m_251_,
        v_e_252_,
        v_varPrefix_253_,
        v_varType_254_,
        v_toExpr_255_,
    );
    leanh::lean_dec_ref(v_e_252_);
    return v_res_256_;
}
pub unsafe fn l_Lean_Meta_Grind_mkLetOfMap(
    mut v_00_u03b1_257_: *mut leanh::LeanObject,
    mut v_x_258_: *mut leanh::LeanObject,
    mut v_x_259_: *mut leanh::LeanObject,
    mut v_m_260_: *mut leanh::LeanObject,
    mut v_e_261_: *mut leanh::LeanObject,
    mut v_varPrefix_262_: *mut leanh::LeanObject,
    mut v_varType_263_: *mut leanh::LeanObject,
    mut v_toExpr_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_265_ = l_Lean_Meta_Grind_mkLetOfMap___redArg(
        v_m_260_,
        v_e_261_,
        v_varPrefix_262_,
        v_varType_263_,
        v_toExpr_264_,
    );
    return v___x_265_;
}
pub unsafe fn l_Lean_Meta_Grind_mkLetOfMap___boxed(
    mut v_00_u03b1_266_: *mut leanh::LeanObject,
    mut v_x_267_: *mut leanh::LeanObject,
    mut v_x_268_: *mut leanh::LeanObject,
    mut v_m_269_: *mut leanh::LeanObject,
    mut v_e_270_: *mut leanh::LeanObject,
    mut v_varPrefix_271_: *mut leanh::LeanObject,
    mut v_varType_272_: *mut leanh::LeanObject,
    mut v_toExpr_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_274_ = l_Lean_Meta_Grind_mkLetOfMap(
        v_00_u03b1_266_,
        v_x_267_,
        v_x_268_,
        v_m_269_,
        v_e_270_,
        v_varPrefix_271_,
        v_varType_272_,
        v_toExpr_273_,
    );
    leanh::lean_dec_ref(v_e_270_);
    leanh::lean_dec_ref(v_x_268_);
    leanh::lean_dec_ref(v_x_267_);
    return v_res_274_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_ProofUtil(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_ProofUtil(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin);
}
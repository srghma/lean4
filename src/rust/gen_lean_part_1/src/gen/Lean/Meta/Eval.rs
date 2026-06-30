// Lean compiler output
// Module: Lean.Meta.Eval
// Imports: Lean.AddDecl Lean.Meta.Check Lean.Util.CollectLevelParams Lean.Compiler.Options
use crate::ffi::{
    lean_array_get_size, lean_array_to_list, lean_array_uget_borrowed, lean_has_compile_error,
    lean_infer_type, lean_mk_array, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Lean::AddDecl::{
    initialize_Lean_AddDecl, l_Lean_addAndCompile, runtime_initialize_Lean_AddDecl,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_markMeta;
use crate::r#gen::Lean::Compiler::Options::{
    initialize_Lean_Compiler_Options, l_Lean_Compiler_compiler_postponeCompile,
    l_Lean_Compiler_compiler_relaxedMetaCheck, runtime_initialize_Lean_Compiler_Options,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_mkFreshUserName, l_Lean_Elab_async, l_Lean_diagnostics, l_Lean_traceBlock___redArg,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_abortCommandExceptionId;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_evalConst___redArg, l_Lean_Environment_importEnv_x3f,
    l_Lean_Environment_isImportedConst, l_Lean_Environment_unlockAsync, l_Lean_Kernel_enableDiag,
    l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_Expr_isConstOf};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{l_Lean_Meta_isExprDefEq, l_Lean_Meta_whnfD};
use crate::r#gen::Lean::Meta::Check::{
    initialize_Lean_Meta_Check, l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg,
    runtime_initialize_Lean_Meta_Check,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::Util::CollectLevelParams::{
    initialize_Lean_Util_CollectLevelParams, l_Lean_collectLevelParams,
    runtime_initialize_Lean_Util_CollectLevelParams,
};
use crate::r#gen::Lean::Util::FoldConsts::l_Lean_Expr_getUsedConstants;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [99, 111, 109, 112, 105, 108, 101, 114, 32, 101, 110, 118, 0],
};
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [95, 116, 109, 112, 0],
};
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value)
            as *mut leanh::LeanObject,
        17409515008221977244 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_value:
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
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_value:
    leanh::LeanStringObject<57> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32,
        101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 44, 32, 105, 116, 32, 99, 111, 110, 116,
        97, 105, 110, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0,
    ],
};
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 97, 116, 32,
        101, 118, 97, 108, 69, 120, 112, 114, 0,
    ],
};
static mut l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_evalExpr___redArg___lam__0___closed__0_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
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
static mut l_Lean_Meta_evalExpr___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_evalExpr___redArg___lam__0___closed__1_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 97, 116, 32,
        96, 101, 118, 97, 108, 69, 120, 112, 114, 96, 32, 0,
    ],
};
static mut l_Lean_Meta_evalExpr___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExpr___redArg___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(
    mut v_e_1145_: *mut leanh::LeanObject,
    mut v___y_1146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1148_: u8 = 0;
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1162_: u8 = 0;
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1168_: u8 = 0;
    let mut v_unused_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1148_ = l_Lean_Expr_hasMVar(v_e_1145_);
                if v___x_1148_ == 0 {
                    v___x_1149_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1149_, 0, v_e_1145_);
                    return v___x_1149_;
                } else {
                    v___x_1150_ = lean_st_ref_get(v___y_1146_);
                    v_mctx_1151_ = leanh::lean_ctor_get(v___x_1150_, 0);
                    leanh::lean_inc_ref(v_mctx_1151_);
                    leanh::lean_dec(v___x_1150_);
                    v___x_1152_ = l_Lean_instantiateMVarsCore(v_mctx_1151_, v_e_1145_);
                    v_fst_1153_ = leanh::lean_ctor_get(v___x_1152_, 0);
                    leanh::lean_inc(v_fst_1153_);
                    v_snd_1154_ = leanh::lean_ctor_get(v___x_1152_, 1);
                    leanh::lean_inc(v_snd_1154_);
                    leanh::lean_dec_ref(v___x_1152_);
                    v___x_1155_ = lean_st_ref_take(v___y_1146_);
                    v_cache_1156_ = leanh::lean_ctor_get(v___x_1155_, 1);
                    v_zetaDeltaFVarIds_1157_ = leanh::lean_ctor_get(v___x_1155_, 2);
                    v_postponed_1158_ = leanh::lean_ctor_get(v___x_1155_, 3);
                    v_diag_1159_ = leanh::lean_ctor_get(v___x_1155_, 4);
                    v_isSharedCheck_1168_ = (!leanh::lean_is_exclusive(v___x_1155_)) as u8;
                    if v_isSharedCheck_1168_ == 0 {
                        v_unused_1169_ = leanh::lean_ctor_get(v___x_1155_, 0);
                        leanh::lean_dec(v_unused_1169_);
                        v___x_1161_ = v___x_1155_;
                        v_isShared_1162_ = v_isSharedCheck_1168_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1159_);
                        leanh::lean_inc(v_postponed_1158_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1157_);
                        leanh::lean_inc(v_cache_1156_);
                        leanh::lean_dec(v___x_1155_);
                        v___x_1161_ = leanh::lean_box(0);
                        v_isShared_1162_ = v_isSharedCheck_1168_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1162_ == 0 {
                    leanh::lean_ctor_set(v___x_1161_, 0, v_snd_1154_);
                    v___x_1164_ = v___x_1161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1167_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_snd_1154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_cache_1156_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1167_,
                        2,
                        v_zetaDeltaFVarIds_1157_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_postponed_1158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_diag_1159_);
                    v___x_1164_ = v_reuseFailAlloc_1167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1165_ = lean_st_ref_set(v___y_1146_, v___x_1164_);
                v___x_1166_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1166_, 0, v_fst_1153_);
                return v___x_1166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg___boxed(
    mut v_e_1170_: *mut leanh::LeanObject,
    mut v___y_1171_: *mut leanh::LeanObject,
    mut v___y_1172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1173_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(
        v_e_1170_,
        v___y_1171_,
    );
    leanh::lean_dec(v___y_1171_);
    return v_res_1173_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(
    mut v_e_1174_: *mut leanh::LeanObject,
    mut v___y_1175_: *mut leanh::LeanObject,
    mut v___y_1176_: *mut leanh::LeanObject,
    mut v___y_1177_: *mut leanh::LeanObject,
    mut v___y_1178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1180_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(
        v_e_1174_,
        v___y_1176_,
    );
    return v___x_1180_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___boxed(
    mut v_e_1181_: *mut leanh::LeanObject,
    mut v___y_1182_: *mut leanh::LeanObject,
    mut v___y_1183_: *mut leanh::LeanObject,
    mut v___y_1184_: *mut leanh::LeanObject,
    mut v___y_1185_: *mut leanh::LeanObject,
    mut v___y_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1187_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(
        v_e_1181_,
        v___y_1182_,
        v___y_1183_,
        v___y_1184_,
        v___y_1185_,
    );
    leanh::lean_dec(v___y_1185_);
    leanh::lean_dec_ref(v___y_1184_);
    leanh::lean_dec(v___y_1183_);
    leanh::lean_dec_ref(v___y_1182_);
    return v_res_1187_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(
    mut v_opts_1188_: *mut leanh::LeanObject,
    mut v_opt_1189_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1190_ = leanh::lean_ctor_get(v_opt_1189_, 0);
    v_defValue_1191_ = leanh::lean_ctor_get(v_opt_1189_, 1);
    v_map_1192_ = leanh::lean_ctor_get(v_opts_1188_, 0);
    v___x_1193_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1192_,
            v_name_1190_,
        );
    if leanh::lean_obj_tag(v___x_1193_) == 0 {
        let mut v___x_1194_: u8 = 0;
        v___x_1194_ = (leanh::lean_unbox(v_defValue_1191_) as u8);
        return v___x_1194_;
    } else {
        let mut v_val_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1195_ = leanh::lean_ctor_get(v___x_1193_, 0);
        leanh::lean_inc(v_val_1195_);
        leanh::lean_dec_ref_known(v___x_1193_, 1);
        if leanh::lean_obj_tag(v_val_1195_) == 1 {
            let mut v_v_1196_: u8 = 0;
            v_v_1196_ = leanh::lean_ctor_get_uint8(v_val_1195_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1195_, 0);
            return v_v_1196_;
        } else {
            let mut v___x_1197_: u8 = 0;
            leanh::lean_dec(v_val_1195_);
            v___x_1197_ = (leanh::lean_unbox(v_defValue_1191_) as u8);
            return v___x_1197_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(
    mut v_opts_1198_: *mut leanh::LeanObject,
    mut v_opt_1199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1200_: u8 = 0;
    let mut v_r_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1200_ =
        l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v_opts_1198_, v_opt_1199_);
    leanh::lean_dec_ref(v_opt_1199_);
    leanh::lean_dec_ref(v_opts_1198_);
    v_r_1201_ = leanh::lean_box((v_res_1200_) as usize);
    return v_r_1201_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(
    mut v_opts_1202_: *mut leanh::LeanObject,
    mut v_opt_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1204_ = leanh::lean_ctor_get(v_opt_1203_, 0);
    v_defValue_1205_ = leanh::lean_ctor_get(v_opt_1203_, 1);
    v_map_1206_ = leanh::lean_ctor_get(v_opts_1202_, 0);
    v___x_1207_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1206_,
            v_name_1204_,
        );
    if leanh::lean_obj_tag(v___x_1207_) == 0 {
        leanh::lean_inc(v_defValue_1205_);
        return v_defValue_1205_;
    } else {
        let mut v_val_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1208_ = leanh::lean_ctor_get(v___x_1207_, 0);
        leanh::lean_inc(v_val_1208_);
        leanh::lean_dec_ref_known(v___x_1207_, 1);
        if leanh::lean_obj_tag(v_val_1208_) == 3 {
            let mut v_v_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1209_ = leanh::lean_ctor_get(v_val_1208_, 0);
            leanh::lean_inc(v_v_1209_);
            leanh::lean_dec_ref_known(v_val_1208_, 1);
            return v_v_1209_;
        } else {
            leanh::lean_dec(v_val_1208_);
            leanh::lean_inc(v_defValue_1205_);
            return v_defValue_1205_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3___boxed(
    mut v_opts_1210_: *mut leanh::LeanObject,
    mut v_opt_1211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1212_ =
        l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v_opts_1210_, v_opt_1211_);
    leanh::lean_dec_ref(v_opt_1211_);
    leanh::lean_dec_ref(v_opts_1210_);
    return v_res_1212_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(
    mut v_msgData_1213_: *mut leanh::LeanObject,
    mut v___y_1214_: *mut leanh::LeanObject,
    mut v___y_1215_: *mut leanh::LeanObject,
    mut v___y_1216_: *mut leanh::LeanObject,
    mut v___y_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1219_ = lean_st_ref_get(v___y_1217_);
    v_env_1220_ = leanh::lean_ctor_get(v___x_1219_, 0);
    leanh::lean_inc_ref(v_env_1220_);
    leanh::lean_dec(v___x_1219_);
    v___x_1221_ = lean_st_ref_get(v___y_1215_);
    v_mctx_1222_ = leanh::lean_ctor_get(v___x_1221_, 0);
    leanh::lean_inc_ref(v_mctx_1222_);
    leanh::lean_dec(v___x_1221_);
    v_lctx_1223_ = leanh::lean_ctor_get(v___y_1214_, 2);
    v_options_1224_ = leanh::lean_ctor_get(v___y_1216_, 2);
    leanh::lean_inc_ref(v_options_1224_);
    leanh::lean_inc_ref(v_lctx_1223_);
    v___x_1225_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1225_, 0, v_env_1220_);
    leanh::lean_ctor_set(v___x_1225_, 1, v_mctx_1222_);
    leanh::lean_ctor_set(v___x_1225_, 2, v_lctx_1223_);
    leanh::lean_ctor_set(v___x_1225_, 3, v_options_1224_);
    v___x_1226_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1226_, 0, v___x_1225_);
    leanh::lean_ctor_set(v___x_1226_, 1, v_msgData_1213_);
    v___x_1227_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1227_, 0, v___x_1226_);
    return v___x_1227_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8___boxed(
    mut v_msgData_1228_: *mut leanh::LeanObject,
    mut v___y_1229_: *mut leanh::LeanObject,
    mut v___y_1230_: *mut leanh::LeanObject,
    mut v___y_1231_: *mut leanh::LeanObject,
    mut v___y_1232_: *mut leanh::LeanObject,
    mut v___y_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1234_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(v_msgData_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
    leanh::lean_dec(v___y_1232_);
    leanh::lean_dec_ref(v___y_1231_);
    leanh::lean_dec(v___y_1230_);
    leanh::lean_dec_ref(v___y_1229_);
    return v_res_1234_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(
    mut v_msg_1235_: *mut leanh::LeanObject,
    mut v___y_1236_: *mut leanh::LeanObject,
    mut v___y_1237_: *mut leanh::LeanObject,
    mut v___y_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1241_ = leanh::lean_ctor_get(v___y_1238_, 5);
                v___x_1242_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(v_msg_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
                v_a_1243_ = leanh::lean_ctor_get(v___x_1242_, 0);
                v_isSharedCheck_1251_ = (!leanh::lean_is_exclusive(v___x_1242_)) as u8;
                if v_isSharedCheck_1251_ == 0 {
                    v___x_1245_ = v___x_1242_;
                    v_isShared_1246_ = v_isSharedCheck_1251_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1243_);
                    leanh::lean_dec(v___x_1242_);
                    v___x_1245_ = leanh::lean_box(0);
                    v_isShared_1246_ = v_isSharedCheck_1251_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1241_);
                v___x_1247_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1247_, 0, v_ref_1241_);
                leanh::lean_ctor_set(v___x_1247_, 1, v_a_1243_);
                if v_isShared_1246_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1245_, 1);
                    leanh::lean_ctor_set(v___x_1245_, 0, v___x_1247_);
                    v___x_1249_ = v___x_1245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
                    v___x_1249_ = v_reuseFailAlloc_1250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg___boxed(
    mut v_msg_1252_: *mut leanh::LeanObject,
    mut v___y_1253_: *mut leanh::LeanObject,
    mut v___y_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(
        v_msg_1252_,
        v___y_1253_,
        v___y_1254_,
        v___y_1255_,
        v___y_1256_,
    );
    leanh::lean_dec(v___y_1256_);
    leanh::lean_dec_ref(v___y_1255_);
    leanh::lean_dec(v___y_1254_);
    leanh::lean_dec_ref(v___y_1253_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(
    mut v_x_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
    mut v___y_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1259_) == 0 {
                    v_a_1265_ = leanh::lean_ctor_get(v_x_1259_, 0);
                    leanh::lean_inc(v_a_1265_);
                    leanh::lean_dec_ref_known(v_x_1259_, 1);
                    v___x_1266_ = l_Lean_stringToMessageData(v_a_1265_);
                    v___x_1267_ =
                        l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(
                            v___x_1266_,
                            v___y_1260_,
                            v___y_1261_,
                            v___y_1262_,
                            v___y_1263_,
                        );
                    return v___x_1267_;
                } else {
                    v_a_1268_ = leanh::lean_ctor_get(v_x_1259_, 0);
                    v_isSharedCheck_1275_ = (!leanh::lean_is_exclusive(v_x_1259_)) as u8;
                    if v_isSharedCheck_1275_ == 0 {
                        v___x_1270_ = v_x_1259_;
                        v_isShared_1271_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1268_);
                        leanh::lean_dec(v_x_1259_);
                        v___x_1270_ = leanh::lean_box(0);
                        v_isShared_1271_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1271_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1270_, 0);
                    v___x_1273_ = v___x_1270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
                    v___x_1273_ = v_reuseFailAlloc_1274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg___boxed(
    mut v_x_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
    mut v___y_1280_: *mut leanh::LeanObject,
    mut v___y_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1282_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
    leanh::lean_dec(v___y_1280_);
    leanh::lean_dec_ref(v___y_1279_);
    leanh::lean_dec(v___y_1278_);
    leanh::lean_dec_ref(v___y_1277_);
    return v_res_1282_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1283_ = leanh::lean_box(0);
    v___x_1284_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_1285_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1285_, 0, v___x_1284_);
    leanh::lean_ctor_set(v___x_1285_, 1, v___x_1283_);
    return v___x_1285_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1287_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0);
    v___x_1288_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1288_, 0, v___x_1287_);
    return v___x_1288_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___boxed(
    mut v___y_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1290_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
    return v_res_1290_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(
    mut v_constName_1291_: *mut leanh::LeanObject,
    mut v_checkMeta_1292_: u8,
    mut v___y_1293_: *mut leanh::LeanObject,
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: u8 = 0;
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1298_ = lean_st_ref_get(v___y_1296_);
                v_env_1299_ = leanh::lean_ctor_get(v___x_1298_, 0);
                leanh::lean_inc_ref(v_env_1299_);
                leanh::lean_dec(v___x_1298_);
                leanh::lean_inc(v_constName_1291_);
                v___x_1300_ = lean_has_compile_error(v_env_1299_, v_constName_1291_);
                if v___x_1300_ == 0 {
                    v___x_1301_ = lean_st_ref_get(v___y_1296_);
                    v_env_1302_ = leanh::lean_ctor_get(v___x_1301_, 0);
                    leanh::lean_inc_ref(v_env_1302_);
                    leanh::lean_dec(v___x_1301_);
                    v_options_1303_ = leanh::lean_ctor_get(v___y_1295_, 2);
                    v___x_1304_ = l_Lean_Environment_evalConst___redArg(
                        v_env_1302_,
                        v_options_1303_,
                        v_constName_1291_,
                        v_checkMeta_1292_,
                    );
                    leanh::lean_dec(v_constName_1291_);
                    leanh::lean_dec_ref(v_env_1302_);
                    v___x_1305_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v___x_1304_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
                    return v___x_1305_;
                } else {
                    v___x_1306_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
                    if leanh::lean_obj_tag(v___x_1306_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1306_, 1);
                        v___x_1307_ = lean_st_ref_get(v___y_1296_);
                        v_env_1308_ = leanh::lean_ctor_get(v___x_1307_, 0);
                        leanh::lean_inc_ref(v_env_1308_);
                        leanh::lean_dec(v___x_1307_);
                        v_options_1309_ = leanh::lean_ctor_get(v___y_1295_, 2);
                        v___x_1310_ = l_Lean_Environment_evalConst___redArg(
                            v_env_1308_,
                            v_options_1309_,
                            v_constName_1291_,
                            v_checkMeta_1292_,
                        );
                        leanh::lean_dec(v_constName_1291_);
                        leanh::lean_dec_ref(v_env_1308_);
                        v___x_1311_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v___x_1310_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
                        return v___x_1311_;
                    } else {
                        leanh::lean_dec(v_constName_1291_);
                        v_a_1312_ = leanh::lean_ctor_get(v___x_1306_, 0);
                        v_isSharedCheck_1319_ =
                            (!leanh::lean_is_exclusive(v___x_1306_)) as u8;
                        if v_isSharedCheck_1319_ == 0 {
                            v___x_1314_ = v___x_1306_;
                            v_isShared_1315_ = v_isSharedCheck_1319_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1312_);
                            leanh::lean_dec(v___x_1306_);
                            v___x_1314_ = leanh::lean_box(0);
                            v_isShared_1315_ = v_isSharedCheck_1319_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1315_ == 0 {
                    v___x_1317_ = v___x_1314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
                    v___x_1317_ = v_reuseFailAlloc_1318_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(
    mut v_constName_1320_: *mut leanh::LeanObject,
    mut v_checkMeta_1321_: *mut leanh::LeanObject,
    mut v___y_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_1327_: u8 = 0;
    let mut v_res_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1327_ = (leanh::lean_unbox(v_checkMeta_1321_) as u8);
    v_res_1328_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(
        v_constName_1320_,
        v_checkMeta_boxed_1327_,
        v___y_1322_,
        v___y_1323_,
        v___y_1324_,
        v___y_1325_,
    );
    leanh::lean_dec(v___y_1325_);
    leanh::lean_dec_ref(v___y_1324_);
    leanh::lean_dec(v___y_1323_);
    leanh::lean_dec_ref(v___y_1322_);
    return v_res_1328_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(
    mut v___x_1329_: *mut leanh::LeanObject,
    mut v_as_1330_: *mut leanh::LeanObject,
    mut v_i_1331_: usize,
    mut v_stop_1332_: usize,
) -> u8 {
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: u8 = 0;
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: usize = 0;
    let mut v___x_1338_: usize = 0;
    let mut v___x_1340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1333_ = lean_usize_dec_eq(v_i_1331_, v_stop_1332_);
                if v___x_1333_ == 0 {
                    v___x_1334_ = 1;
                    v___x_1335_ = lean_array_uget_borrowed(v_as_1330_, v_i_1331_);
                    v___x_1336_ = l_Lean_Environment_isImportedConst(v___x_1329_, v___x_1335_);
                    if v___x_1336_ == 0 {
                        return v___x_1334_;
                    } else {
                        if v___x_1333_ == 0 {
                            v___x_1337_ = 1usize;
                            v___x_1338_ = lean_usize_add(v_i_1331_, v___x_1337_);
                            v_i_1331_ = v___x_1338_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1334_;
                        }
                    }
                } else {
                    v___x_1340_ = 0;
                    return v___x_1340_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(
    mut v___x_1341_: *mut leanh::LeanObject,
    mut v_as_1342_: *mut leanh::LeanObject,
    mut v_i_1343_: *mut leanh::LeanObject,
    mut v_stop_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1345_: usize = 0;
    let mut v_stop_boxed_1346_: usize = 0;
    let mut v_res_1347_: u8 = 0;
    let mut v_r_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1345_ = leanh::lean_unbox_usize(v_i_1343_);
    leanh::lean_dec(v_i_1343_);
    v_stop_boxed_1346_ = leanh::lean_unbox_usize(v_stop_1344_);
    leanh::lean_dec(v_stop_1344_);
    v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v___x_1341_, v_as_1342_, v_i_boxed_1345_, v_stop_boxed_1346_);
    leanh::lean_dec_ref(v_as_1342_);
    leanh::lean_dec_ref(v___x_1341_);
    v_r_1348_ = leanh::lean_box((v_res_1347_) as usize);
    return v_r_1348_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(
    mut v_o_1352_: *mut leanh::LeanObject,
    mut v_k_1353_: *mut leanh::LeanObject,
    mut v_v_1354_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1356_: u8 = 0;
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1355_ = leanh::lean_ctor_get(v_o_1352_, 0);
                v_hasTrace_1356_ = leanh::lean_ctor_get_uint8(
                    v_o_1352_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1370_ = (!leanh::lean_is_exclusive(v_o_1352_)) as u8;
                if v_isSharedCheck_1370_ == 0 {
                    v___x_1358_ = v_o_1352_;
                    v_isShared_1359_ = v_isSharedCheck_1370_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_1355_);
                    leanh::lean_dec(v_o_1352_);
                    v___x_1358_ = leanh::lean_box(0);
                    v_isShared_1359_ = v_isSharedCheck_1370_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1360_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_1360_, 0 as u32, v_v_1354_);
                leanh::lean_inc(v_k_1353_);
                v___x_1361_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1353_, v___x_1360_, v_map_1355_);
                if v_hasTrace_1356_ == 0 {
                    v___x_1362_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1;
                    v___x_1363_ = l_Lean_Name_isPrefixOf(v___x_1362_, v_k_1353_);
                    leanh::lean_dec(v_k_1353_);
                    if v_isShared_1359_ == 0 {
                        leanh::lean_ctor_set(v___x_1358_, 0, v___x_1361_);
                        v___x_1365_ = v___x_1358_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1366_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1361_);
                        v___x_1365_ = v_reuseFailAlloc_1366_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_1353_);
                    if v_isShared_1359_ == 0 {
                        leanh::lean_ctor_set(v___x_1358_, 0, v___x_1361_);
                        v___x_1368_ = v___x_1358_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1369_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1361_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1369_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_1356_,
                        );
                        v___x_1368_ = v_reuseFailAlloc_1369_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1365_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1363_,
                );
                return v___x_1365_;
            }
            3 => {
                return v___x_1368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___boxed(
    mut v_o_1371_: *mut leanh::LeanObject,
    mut v_k_1372_: *mut leanh::LeanObject,
    mut v_v_1373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_1374_: u8 = 0;
    let mut v_res_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_1374_ = (leanh::lean_unbox(v_v_1373_) as u8);
    v_res_1375_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(
            v_o_1371_,
            v_k_1372_,
            v_v_boxed_1374_,
        );
    return v_res_1375_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(
    mut v_opts_1376_: *mut leanh::LeanObject,
    mut v_opt_1377_: *mut leanh::LeanObject,
    mut v_val_1378_: u8,
) -> *mut leanh::LeanObject {
    let mut v_name_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1379_ = leanh::lean_ctor_get(v_opt_1377_, 0);
    leanh::lean_inc(v_name_1379_);
    leanh::lean_dec_ref(v_opt_1377_);
    v___x_1380_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(
            v_opts_1376_,
            v_name_1379_,
            v_val_1378_,
        );
    return v___x_1380_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1___boxed(
    mut v_opts_1381_: *mut leanh::LeanObject,
    mut v_opt_1382_: *mut leanh::LeanObject,
    mut v_val_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_1384_: u8 = 0;
    let mut v_res_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_1384_ = (leanh::lean_unbox(v_val_1383_) as u8);
    v_res_1385_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(
        v_opts_1381_,
        v_opt_1382_,
        v_val_boxed_1384_,
    );
    return v_res_1385_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1386_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1387_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once),
        _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0,
    );
    v___x_1388_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1388_, 0, v___x_1387_);
    return v___x_1388_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1389_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once),
        _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1,
    );
    v___x_1390_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1390_, 0, v___x_1389_);
    leanh::lean_ctor_set(v___x_1390_, 1, v___x_1389_);
    return v___x_1390_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once),
        _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1,
    );
    v___x_1392_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
    leanh::lean_ctor_set(v___x_1392_, 1, v___x_1391_);
    leanh::lean_ctor_set(v___x_1392_, 2, v___x_1391_);
    leanh::lean_ctor_set(v___x_1392_, 3, v___x_1391_);
    leanh::lean_ctor_set(v___x_1392_, 4, v___x_1391_);
    leanh::lean_ctor_set(v___x_1392_, 5, v___x_1391_);
    return v___x_1392_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = leanh::lean_box(0);
    v___x_1398_ = leanh::lean_unsigned_to_nat(16);
    v___x_1399_ = lean_mk_array(v___x_1398_, v___x_1397_);
    return v___x_1399_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once),
        _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7,
    );
    v___x_1401_ = leanh::lean_unsigned_to_nat(0);
    v___x_1402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1402_, 0, v___x_1401_);
    leanh::lean_ctor_set(v___x_1402_, 1, v___x_1400_);
    return v___x_1402_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9;
    v___x_1406_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once),
        _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8,
    );
    v___x_1407_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1407_, 0, v___x_1406_);
    leanh::lean_ctor_set(v___x_1407_, 1, v___x_1406_);
    leanh::lean_ctor_set(v___x_1407_, 2, v___x_1405_);
    return v___x_1407_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11;
    v___x_1410_ = l_Lean_stringToMessageData(v___x_1409_);
    return v___x_1410_;
}
pub unsafe fn l_Lean_Meta_evalExprCore___redArg___lam__0(
    mut v_checkMeta_1411_: u8,
    mut v_checkType_1412_: *mut leanh::LeanObject,
    mut v_safety_1413_: u8,
    mut v_value_1414_: *mut leanh::LeanObject,
    mut v___y_1415_: *mut leanh::LeanObject,
    mut v___y_1416_: *mut leanh::LeanObject,
    mut v___y_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1421_: u8 = 0;
    let mut v___y_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1425_: u8 = 0;
    let mut v___y_1426_: u8 = 0;
    let mut v___y_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1441_: u8 = 0;
    let mut v_inheritedTraceOptions_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut v___y_1457_: u8 = 0;
    let mut v___y_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: u8 = 0;
    let mut v___y_1462_: u8 = 0;
    let mut v___y_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1479_: u8 = 0;
    let mut v_inheritedTraceOptions_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1482_: u8 = 0;
    let mut v___y_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1492_: u8 = 0;
    let mut v___y_1493_: u8 = 0;
    let mut v___y_1494_: u8 = 0;
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1506_: u8 = 0;
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_unused_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: u8 = 0;
    let mut v___y_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1517_: u8 = 0;
    let mut v___y_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: u8 = 0;
    let mut v___y_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1540_: u8 = 0;
    let mut v_inheritedTraceOptions_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1544_: u8 = 0;
    let mut v_env_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: u8 = 0;
    let mut v___x_1552_: u8 = 0;
    let mut v_reuseFailAlloc_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut v_unused_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: u8 = 0;
    let mut v___y_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: u8 = 0;
    let mut v___y_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1570_: u8 = 0;
    let mut v___y_1571_: u8 = 0;
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1589_: u8 = 0;
    let mut v_unused_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1592_: u8 = 0;
    let mut v___y_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1596_: u8 = 0;
    let mut v___y_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1598_: u8 = 0;
    let mut v___y_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1616_: u8 = 0;
    let mut v_inheritedTraceOptions_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v_env_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: u8 = 0;
    let mut v_reuseFailAlloc_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1631_: u8 = 0;
    let mut v_unused_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1635_: u8 = 0;
    let mut v___y_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1643_: u8 = 0;
    let mut v___y_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1645_: u8 = 0;
    let mut v___y_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1647_: u8 = 0;
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1659_: u8 = 0;
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut v_unused_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1690_: u8 = 0;
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: u8 = 0;
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: u8 = 0;
    let mut v_a_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1732_: u8 = 0;
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1736_: u8 = 0;
    let mut v_reuseFailAlloc_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_unused_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_unused_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1746_: u8 = 0;
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut v_a_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1758_: u8 = 0;
    let mut v___y_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: u8 = 0;
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1788_: u8 = 0;
    let mut v_a_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v_a_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut v_nextMacroScope_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v_unused_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v_env_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: usize = 0;
    let mut v___x_1852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1832_ = lean_st_ref_get(v___y_1418_);
                leanh::lean_inc_ref(v_value_1414_);
                v___x_1845_ = l_Lean_Expr_getUsedConstants(v_value_1414_);
                v___x_1846_ = leanh::lean_unsigned_to_nat(0);
                v___x_1847_ = lean_array_get_size(v___x_1845_);
                v___x_1848_ = lean_nat_dec_lt(v___x_1846_, v___x_1847_);
                if v___x_1848_ == 0 {
                    leanh::lean_dec_ref(v___x_1845_);
                    leanh::lean_dec(v___x_1832_);
                    state = 41;
                    continue;
                } else {
                    if v___x_1848_ == 0 {
                        leanh::lean_dec_ref(v___x_1845_);
                        leanh::lean_dec(v___x_1832_);
                        state = 41;
                        continue;
                    } else {
                        v_env_1849_ = leanh::lean_ctor_get(v___x_1832_, 0);
                        leanh::lean_inc_ref(v_env_1849_);
                        leanh::lean_dec(v___x_1832_);
                        v___x_1850_ = 0usize;
                        v___x_1851_ = lean_usize_of_nat(v___x_1847_);
                        v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_1849_, v___x_1845_, v___x_1850_, v___x_1851_);
                        leanh::lean_dec_ref(v___x_1845_);
                        leanh::lean_dec_ref(v_env_1849_);
                        if v___x_1852_ == 0 {
                            state = 41;
                            continue;
                        } else {
                            v___y_1760_ = v___y_1415_;
                            v___y_1761_ = v___y_1416_;
                            v___y_1762_ = v___y_1417_;
                            v___y_1763_ = v___y_1418_;
                            state = 31;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1444_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(
                    v___y_1424_,
                    v___y_1427_,
                );
                v___x_1445_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_1445_, 0, v_fileName_1430_);
                leanh::lean_ctor_set(v___x_1445_, 1, v_fileMap_1431_);
                leanh::lean_ctor_set(v___x_1445_, 2, v___y_1424_);
                leanh::lean_ctor_set(v___x_1445_, 3, v_currRecDepth_1432_);
                leanh::lean_ctor_set(v___x_1445_, 4, v___x_1444_);
                leanh::lean_ctor_set(v___x_1445_, 5, v_ref_1433_);
                leanh::lean_ctor_set(v___x_1445_, 6, v_currNamespace_1434_);
                leanh::lean_ctor_set(v___x_1445_, 7, v_openDecls_1435_);
                leanh::lean_ctor_set(v___x_1445_, 8, v_initHeartbeats_1436_);
                leanh::lean_ctor_set(v___x_1445_, 9, v_maxHeartbeats_1437_);
                leanh::lean_ctor_set(v___x_1445_, 10, v_quotContext_1438_);
                leanh::lean_ctor_set(v___x_1445_, 11, v_currMacroScope_1439_);
                leanh::lean_ctor_set(v___x_1445_, 12, v_cancelTk_x3f_1440_);
                leanh::lean_ctor_set(v___x_1445_, 13, v_inheritedTraceOptions_1442_);
                leanh::lean_ctor_set_uint8(
                    v___x_1445_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_1426_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1445_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1441_,
                );
                v___x_1446_ = l_Lean_addAndCompile(
                    v___y_1422_,
                    v___y_1421_,
                    v___y_1425_,
                    v___x_1445_,
                    v___y_1443_,
                );
                if leanh::lean_obj_tag(v___x_1446_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1446_, 1);
                    v___x_1447_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(
                        v___y_1429_,
                        v_checkMeta_1411_,
                        v___y_1423_,
                        v___y_1428_,
                        v___x_1445_,
                        v___y_1443_,
                    );
                    leanh::lean_dec(v___y_1443_);
                    leanh::lean_dec_ref_known(v___x_1445_, 14);
                    leanh::lean_dec(v___y_1428_);
                    leanh::lean_dec_ref(v___y_1423_);
                    return v___x_1447_;
                } else {
                    leanh::lean_dec_ref_known(v___x_1445_, 14);
                    leanh::lean_dec(v___y_1443_);
                    leanh::lean_dec(v___y_1429_);
                    leanh::lean_dec(v___y_1428_);
                    leanh::lean_dec_ref(v___y_1423_);
                    v_a_1448_ = leanh::lean_ctor_get(v___x_1446_, 0);
                    v_isSharedCheck_1455_ = (!leanh::lean_is_exclusive(v___x_1446_)) as u8;
                    if v_isSharedCheck_1455_ == 0 {
                        v___x_1450_ = v___x_1446_;
                        v_isShared_1451_ = v_isSharedCheck_1455_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1448_);
                        leanh::lean_dec(v___x_1446_);
                        v___x_1450_ = leanh::lean_box(0);
                        v_isShared_1451_ = v_isSharedCheck_1455_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1451_ == 0 {
                    v___x_1453_ = v___x_1450_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1454_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
                    v___x_1453_ = v_reuseFailAlloc_1454_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1453_;
            }
            4 => {
                v_fileName_1468_ = leanh::lean_ctor_get(v___y_1466_, 0);
                leanh::lean_inc_ref(v_fileName_1468_);
                v_fileMap_1469_ = leanh::lean_ctor_get(v___y_1466_, 1);
                leanh::lean_inc_ref(v_fileMap_1469_);
                v_currRecDepth_1470_ = leanh::lean_ctor_get(v___y_1466_, 3);
                leanh::lean_inc(v_currRecDepth_1470_);
                v_ref_1471_ = leanh::lean_ctor_get(v___y_1466_, 5);
                leanh::lean_inc(v_ref_1471_);
                v_currNamespace_1472_ = leanh::lean_ctor_get(v___y_1466_, 6);
                leanh::lean_inc(v_currNamespace_1472_);
                v_openDecls_1473_ = leanh::lean_ctor_get(v___y_1466_, 7);
                leanh::lean_inc(v_openDecls_1473_);
                v_initHeartbeats_1474_ = leanh::lean_ctor_get(v___y_1466_, 8);
                leanh::lean_inc(v_initHeartbeats_1474_);
                v_maxHeartbeats_1475_ = leanh::lean_ctor_get(v___y_1466_, 9);
                leanh::lean_inc(v_maxHeartbeats_1475_);
                v_quotContext_1476_ = leanh::lean_ctor_get(v___y_1466_, 10);
                leanh::lean_inc(v_quotContext_1476_);
                v_currMacroScope_1477_ = leanh::lean_ctor_get(v___y_1466_, 11);
                leanh::lean_inc(v_currMacroScope_1477_);
                v_cancelTk_x3f_1478_ = leanh::lean_ctor_get(v___y_1466_, 12);
                leanh::lean_inc(v_cancelTk_x3f_1478_);
                v_suppressElabErrors_1479_ = leanh::lean_ctor_get_uint8(
                    v___y_1466_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1480_ = leanh::lean_ctor_get(v___y_1466_, 13);
                leanh::lean_inc_ref(v_inheritedTraceOptions_1480_);
                leanh::lean_dec_ref(v___y_1466_);
                v___y_1421_ = v___y_1457_;
                v___y_1422_ = v___y_1458_;
                v___y_1423_ = v___y_1459_;
                v___y_1424_ = v___y_1460_;
                v___y_1425_ = v___y_1461_;
                v___y_1426_ = v___y_1462_;
                v___y_1427_ = v___y_1463_;
                v___y_1428_ = v___y_1464_;
                v___y_1429_ = v___y_1465_;
                v_fileName_1430_ = v_fileName_1468_;
                v_fileMap_1431_ = v_fileMap_1469_;
                v_currRecDepth_1432_ = v_currRecDepth_1470_;
                v_ref_1433_ = v_ref_1471_;
                v_currNamespace_1434_ = v_currNamespace_1472_;
                v_openDecls_1435_ = v_openDecls_1473_;
                v_initHeartbeats_1436_ = v_initHeartbeats_1474_;
                v_maxHeartbeats_1437_ = v_maxHeartbeats_1475_;
                v_quotContext_1438_ = v_quotContext_1476_;
                v_currMacroScope_1439_ = v_currMacroScope_1477_;
                v_cancelTk_x3f_1440_ = v_cancelTk_x3f_1478_;
                v_suppressElabErrors_1441_ = v_suppressElabErrors_1479_;
                v_inheritedTraceOptions_1442_ = v_inheritedTraceOptions_1480_;
                v___y_1443_ = v___y_1467_;
                state = 1;
                continue;
            }
            5 => {
                if v___y_1494_ == 0 {
                    v___x_1495_ = lean_st_ref_take(v___y_1488_);
                    v_env_1496_ = leanh::lean_ctor_get(v___x_1495_, 0);
                    v_nextMacroScope_1497_ = leanh::lean_ctor_get(v___x_1495_, 1);
                    v_ngen_1498_ = leanh::lean_ctor_get(v___x_1495_, 2);
                    v_auxDeclNGen_1499_ = leanh::lean_ctor_get(v___x_1495_, 3);
                    v_traceState_1500_ = leanh::lean_ctor_get(v___x_1495_, 4);
                    v_messages_1501_ = leanh::lean_ctor_get(v___x_1495_, 6);
                    v_infoState_1502_ = leanh::lean_ctor_get(v___x_1495_, 7);
                    v_snapshotTasks_1503_ = leanh::lean_ctor_get(v___x_1495_, 8);
                    v_isSharedCheck_1512_ = (!leanh::lean_is_exclusive(v___x_1495_)) as u8;
                    if v_isSharedCheck_1512_ == 0 {
                        v_unused_1513_ = leanh::lean_ctor_get(v___x_1495_, 5);
                        leanh::lean_dec(v_unused_1513_);
                        v___x_1505_ = v___x_1495_;
                        v_isShared_1506_ = v_isSharedCheck_1512_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_1503_);
                        leanh::lean_inc(v_infoState_1502_);
                        leanh::lean_inc(v_messages_1501_);
                        leanh::lean_inc(v_traceState_1500_);
                        leanh::lean_inc(v_auxDeclNGen_1499_);
                        leanh::lean_inc(v_ngen_1498_);
                        leanh::lean_inc(v_nextMacroScope_1497_);
                        leanh::lean_inc(v_env_1496_);
                        leanh::lean_dec(v___x_1495_);
                        v___x_1505_ = leanh::lean_box(0);
                        v_isShared_1506_ = v_isSharedCheck_1512_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___y_1457_ = v___y_1482_;
                    v___y_1458_ = v___y_1489_;
                    v___y_1459_ = v___y_1490_;
                    v___y_1460_ = v___y_1491_;
                    v___y_1461_ = v___y_1493_;
                    v___y_1462_ = v___y_1492_;
                    v___y_1463_ = v___y_1485_;
                    v___y_1464_ = v___y_1486_;
                    v___y_1465_ = v___y_1487_;
                    v___y_1466_ = v___y_1483_;
                    v___y_1467_ = v___y_1488_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_1507_ = l_Lean_Kernel_enableDiag(v_env_1496_, v___y_1492_);
                leanh::lean_inc_ref(v___y_1484_);
                if v_isShared_1506_ == 0 {
                    leanh::lean_ctor_set(v___x_1505_, 5, v___y_1484_);
                    leanh::lean_ctor_set(v___x_1505_, 0, v___x_1507_);
                    v___x_1509_ = v___x_1505_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1511_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_nextMacroScope_1497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_ngen_1498_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_auxDeclNGen_1499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_traceState_1500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 5, v___y_1484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 6, v_messages_1501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 7, v_infoState_1502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 8, v_snapshotTasks_1503_);
                    v___x_1509_ = v_reuseFailAlloc_1511_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1510_ = lean_st_ref_set(v___y_1488_, v___x_1509_);
                v___y_1457_ = v___y_1482_;
                v___y_1458_ = v___y_1489_;
                v___y_1459_ = v___y_1490_;
                v___y_1460_ = v___y_1491_;
                v___y_1461_ = v___y_1493_;
                v___y_1462_ = v___y_1492_;
                v___y_1463_ = v___y_1485_;
                v___y_1464_ = v___y_1486_;
                v___y_1465_ = v___y_1487_;
                v___y_1466_ = v___y_1483_;
                v___y_1467_ = v___y_1488_;
                state = 4;
                continue;
            }
            8 => {
                v___x_1528_ = lean_st_ref_get(v___y_1527_);
                v_fileName_1529_ = leanh::lean_ctor_get(v___y_1526_, 0);
                v_fileMap_1530_ = leanh::lean_ctor_get(v___y_1526_, 1);
                v_currRecDepth_1531_ = leanh::lean_ctor_get(v___y_1526_, 3);
                v_ref_1532_ = leanh::lean_ctor_get(v___y_1526_, 5);
                v_currNamespace_1533_ = leanh::lean_ctor_get(v___y_1526_, 6);
                v_openDecls_1534_ = leanh::lean_ctor_get(v___y_1526_, 7);
                v_initHeartbeats_1535_ = leanh::lean_ctor_get(v___y_1526_, 8);
                v_maxHeartbeats_1536_ = leanh::lean_ctor_get(v___y_1526_, 9);
                v_quotContext_1537_ = leanh::lean_ctor_get(v___y_1526_, 10);
                v_currMacroScope_1538_ = leanh::lean_ctor_get(v___y_1526_, 11);
                v_cancelTk_x3f_1539_ = leanh::lean_ctor_get(v___y_1526_, 12);
                v_suppressElabErrors_1540_ = leanh::lean_ctor_get_uint8(
                    v___y_1526_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1541_ = leanh::lean_ctor_get(v___y_1526_, 13);
                v_isSharedCheck_1554_ = (!leanh::lean_is_exclusive(v___y_1526_)) as u8;
                if v_isSharedCheck_1554_ == 0 {
                    v_unused_1555_ = leanh::lean_ctor_get(v___y_1526_, 4);
                    leanh::lean_dec(v_unused_1555_);
                    v_unused_1556_ = leanh::lean_ctor_get(v___y_1526_, 2);
                    leanh::lean_dec(v_unused_1556_);
                    v___x_1543_ = v___y_1526_;
                    v_isShared_1544_ = v_isSharedCheck_1554_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_inheritedTraceOptions_1541_);
                    leanh::lean_inc(v_cancelTk_x3f_1539_);
                    leanh::lean_inc(v_currMacroScope_1538_);
                    leanh::lean_inc(v_quotContext_1537_);
                    leanh::lean_inc(v_maxHeartbeats_1536_);
                    leanh::lean_inc(v_initHeartbeats_1535_);
                    leanh::lean_inc(v_openDecls_1534_);
                    leanh::lean_inc(v_currNamespace_1533_);
                    leanh::lean_inc(v_ref_1532_);
                    leanh::lean_inc(v_currRecDepth_1531_);
                    leanh::lean_inc(v_fileMap_1530_);
                    leanh::lean_inc(v_fileName_1529_);
                    leanh::lean_dec(v___y_1526_);
                    v___x_1543_ = leanh::lean_box(0);
                    v_isShared_1544_ = v_isSharedCheck_1554_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_env_1545_ = leanh::lean_ctor_get(v___x_1528_, 0);
                leanh::lean_inc_ref(v_env_1545_);
                leanh::lean_dec(v___x_1528_);
                v___x_1546_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(
                    v___y_1525_,
                    v___y_1522_,
                );
                leanh::lean_inc_ref(v_inheritedTraceOptions_1541_);
                leanh::lean_inc(v_cancelTk_x3f_1539_);
                leanh::lean_inc(v_currMacroScope_1538_);
                leanh::lean_inc(v_quotContext_1537_);
                leanh::lean_inc(v_maxHeartbeats_1536_);
                leanh::lean_inc(v_initHeartbeats_1535_);
                leanh::lean_inc(v_openDecls_1534_);
                leanh::lean_inc(v_currNamespace_1533_);
                leanh::lean_inc(v_ref_1532_);
                leanh::lean_inc(v_currRecDepth_1531_);
                leanh::lean_inc_ref(v___y_1525_);
                leanh::lean_inc_ref(v_fileMap_1530_);
                leanh::lean_inc_ref(v_fileName_1529_);
                if v_isShared_1544_ == 0 {
                    leanh::lean_ctor_set(v___x_1543_, 4, v___x_1546_);
                    leanh::lean_ctor_set(v___x_1543_, 2, v___y_1525_);
                    v___x_1548_ = v___x_1543_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1553_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_fileName_1529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_fileMap_1530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 2, v___y_1525_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_currRecDepth_1531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 4, v___x_1546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 5, v_ref_1532_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 6, v_currNamespace_1533_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 7, v_openDecls_1534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 8, v_initHeartbeats_1535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 9, v_maxHeartbeats_1536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 10, v_quotContext_1537_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 11, v_currMacroScope_1538_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 12, v_cancelTk_x3f_1539_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1553_,
                        13,
                        v_inheritedTraceOptions_1541_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1553_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1540_,
                    );
                    v___x_1548_ = v_reuseFailAlloc_1553_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1548_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_1515_,
                );
                v___x_1549_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
                v___x_1550_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(
                    v___y_1525_,
                    v___x_1549_,
                    v___y_1517_,
                );
                v___x_1551_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(
                    v___x_1550_,
                    v___y_1516_,
                );
                v___x_1552_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1545_);
                leanh::lean_dec_ref(v_env_1545_);
                if v___x_1552_ == 0 {
                    if v___x_1551_ == 0 {
                        leanh::lean_dec_ref(v___x_1548_);
                        v___y_1421_ = v___y_1517_;
                        v___y_1422_ = v___y_1518_;
                        v___y_1423_ = v___y_1519_;
                        v___y_1424_ = v___x_1550_;
                        v___y_1425_ = v___y_1521_;
                        v___y_1426_ = v___x_1551_;
                        v___y_1427_ = v___y_1522_;
                        v___y_1428_ = v___y_1524_;
                        v___y_1429_ = v___y_1523_;
                        v_fileName_1430_ = v_fileName_1529_;
                        v_fileMap_1431_ = v_fileMap_1530_;
                        v_currRecDepth_1432_ = v_currRecDepth_1531_;
                        v_ref_1433_ = v_ref_1532_;
                        v_currNamespace_1434_ = v_currNamespace_1533_;
                        v_openDecls_1435_ = v_openDecls_1534_;
                        v_initHeartbeats_1436_ = v_initHeartbeats_1535_;
                        v_maxHeartbeats_1437_ = v_maxHeartbeats_1536_;
                        v_quotContext_1438_ = v_quotContext_1537_;
                        v_currMacroScope_1439_ = v_currMacroScope_1538_;
                        v_cancelTk_x3f_1440_ = v_cancelTk_x3f_1539_;
                        v_suppressElabErrors_1441_ = v_suppressElabErrors_1540_;
                        v_inheritedTraceOptions_1442_ = v_inheritedTraceOptions_1541_;
                        v___y_1443_ = v___y_1527_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_inheritedTraceOptions_1541_);
                        leanh::lean_dec(v_cancelTk_x3f_1539_);
                        leanh::lean_dec(v_currMacroScope_1538_);
                        leanh::lean_dec(v_quotContext_1537_);
                        leanh::lean_dec(v_maxHeartbeats_1536_);
                        leanh::lean_dec(v_initHeartbeats_1535_);
                        leanh::lean_dec(v_openDecls_1534_);
                        leanh::lean_dec(v_currNamespace_1533_);
                        leanh::lean_dec(v_ref_1532_);
                        leanh::lean_dec(v_currRecDepth_1531_);
                        leanh::lean_dec_ref(v_fileMap_1530_);
                        leanh::lean_dec_ref(v_fileName_1529_);
                        v___y_1482_ = v___y_1517_;
                        v___y_1483_ = v___x_1548_;
                        v___y_1484_ = v___y_1520_;
                        v___y_1485_ = v___y_1522_;
                        v___y_1486_ = v___y_1524_;
                        v___y_1487_ = v___y_1523_;
                        v___y_1488_ = v___y_1527_;
                        v___y_1489_ = v___y_1518_;
                        v___y_1490_ = v___y_1519_;
                        v___y_1491_ = v___x_1550_;
                        v___y_1492_ = v___x_1551_;
                        v___y_1493_ = v___y_1521_;
                        v___y_1494_ = v___x_1552_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inheritedTraceOptions_1541_);
                    leanh::lean_dec(v_cancelTk_x3f_1539_);
                    leanh::lean_dec(v_currMacroScope_1538_);
                    leanh::lean_dec(v_quotContext_1537_);
                    leanh::lean_dec(v_maxHeartbeats_1536_);
                    leanh::lean_dec(v_initHeartbeats_1535_);
                    leanh::lean_dec(v_openDecls_1534_);
                    leanh::lean_dec(v_currNamespace_1533_);
                    leanh::lean_dec(v_ref_1532_);
                    leanh::lean_dec(v_currRecDepth_1531_);
                    leanh::lean_dec_ref(v_fileMap_1530_);
                    leanh::lean_dec_ref(v_fileName_1529_);
                    v___y_1482_ = v___y_1517_;
                    v___y_1483_ = v___x_1548_;
                    v___y_1484_ = v___y_1520_;
                    v___y_1485_ = v___y_1522_;
                    v___y_1486_ = v___y_1524_;
                    v___y_1487_ = v___y_1523_;
                    v___y_1488_ = v___y_1527_;
                    v___y_1489_ = v___y_1518_;
                    v___y_1490_ = v___y_1519_;
                    v___y_1491_ = v___x_1550_;
                    v___y_1492_ = v___x_1551_;
                    v___y_1493_ = v___y_1521_;
                    v___y_1494_ = v___x_1551_;
                    state = 5;
                    continue;
                }
            }
            11 => {
                if v___y_1571_ == 0 {
                    v___x_1572_ = lean_st_ref_take(v___y_1568_);
                    v_env_1573_ = leanh::lean_ctor_get(v___x_1572_, 0);
                    v_nextMacroScope_1574_ = leanh::lean_ctor_get(v___x_1572_, 1);
                    v_ngen_1575_ = leanh::lean_ctor_get(v___x_1572_, 2);
                    v_auxDeclNGen_1576_ = leanh::lean_ctor_get(v___x_1572_, 3);
                    v_traceState_1577_ = leanh::lean_ctor_get(v___x_1572_, 4);
                    v_messages_1578_ = leanh::lean_ctor_get(v___x_1572_, 6);
                    v_infoState_1579_ = leanh::lean_ctor_get(v___x_1572_, 7);
                    v_snapshotTasks_1580_ = leanh::lean_ctor_get(v___x_1572_, 8);
                    v_isSharedCheck_1589_ = (!leanh::lean_is_exclusive(v___x_1572_)) as u8;
                    if v_isSharedCheck_1589_ == 0 {
                        v_unused_1590_ = leanh::lean_ctor_get(v___x_1572_, 5);
                        leanh::lean_dec(v_unused_1590_);
                        v___x_1582_ = v___x_1572_;
                        v_isShared_1583_ = v_isSharedCheck_1589_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_1580_);
                        leanh::lean_inc(v_infoState_1579_);
                        leanh::lean_inc(v_messages_1578_);
                        leanh::lean_inc(v_traceState_1577_);
                        leanh::lean_inc(v_auxDeclNGen_1576_);
                        leanh::lean_inc(v_ngen_1575_);
                        leanh::lean_inc(v_nextMacroScope_1574_);
                        leanh::lean_inc(v_env_1573_);
                        leanh::lean_dec(v___x_1572_);
                        v___x_1582_ = leanh::lean_box(0);
                        v_isShared_1583_ = v_isSharedCheck_1589_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___y_1515_ = v___y_1558_;
                    v___y_1516_ = v___y_1566_;
                    v___y_1517_ = v___y_1560_;
                    v___y_1518_ = v___y_1567_;
                    v___y_1519_ = v___y_1569_;
                    v___y_1520_ = v___y_1561_;
                    v___y_1521_ = v___y_1570_;
                    v___y_1522_ = v___y_1562_;
                    v___y_1523_ = v___y_1563_;
                    v___y_1524_ = v___y_1564_;
                    v___y_1525_ = v___y_1565_;
                    v___y_1526_ = v___y_1559_;
                    v___y_1527_ = v___y_1568_;
                    state = 8;
                    continue;
                }
            }
            12 => {
                v___x_1584_ = l_Lean_Kernel_enableDiag(v_env_1573_, v___y_1558_);
                leanh::lean_inc_ref(v___y_1561_);
                if v_isShared_1583_ == 0 {
                    leanh::lean_ctor_set(v___x_1582_, 5, v___y_1561_);
                    leanh::lean_ctor_set(v___x_1582_, 0, v___x_1584_);
                    v___x_1586_ = v___x_1582_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1588_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_nextMacroScope_1574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_ngen_1575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 3, v_auxDeclNGen_1576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 4, v_traceState_1577_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 5, v___y_1561_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 6, v_messages_1578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 7, v_infoState_1579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 8, v_snapshotTasks_1580_);
                    v___x_1586_ = v_reuseFailAlloc_1588_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1587_ = lean_st_ref_set(v___y_1568_, v___x_1586_);
                v___y_1515_ = v___y_1558_;
                v___y_1516_ = v___y_1566_;
                v___y_1517_ = v___y_1560_;
                v___y_1518_ = v___y_1567_;
                v___y_1519_ = v___y_1569_;
                v___y_1520_ = v___y_1561_;
                v___y_1521_ = v___y_1570_;
                v___y_1522_ = v___y_1562_;
                v___y_1523_ = v___y_1563_;
                v___y_1524_ = v___y_1564_;
                v___y_1525_ = v___y_1565_;
                v___y_1526_ = v___y_1559_;
                v___y_1527_ = v___y_1568_;
                state = 8;
                continue;
            }
            14 => {
                v___x_1604_ = lean_st_ref_get(v___y_1603_);
                v_fileName_1605_ = leanh::lean_ctor_get(v___y_1602_, 0);
                v_fileMap_1606_ = leanh::lean_ctor_get(v___y_1602_, 1);
                v_currRecDepth_1607_ = leanh::lean_ctor_get(v___y_1602_, 3);
                v_ref_1608_ = leanh::lean_ctor_get(v___y_1602_, 5);
                v_currNamespace_1609_ = leanh::lean_ctor_get(v___y_1602_, 6);
                v_openDecls_1610_ = leanh::lean_ctor_get(v___y_1602_, 7);
                v_initHeartbeats_1611_ = leanh::lean_ctor_get(v___y_1602_, 8);
                v_maxHeartbeats_1612_ = leanh::lean_ctor_get(v___y_1602_, 9);
                v_quotContext_1613_ = leanh::lean_ctor_get(v___y_1602_, 10);
                v_currMacroScope_1614_ = leanh::lean_ctor_get(v___y_1602_, 11);
                v_cancelTk_x3f_1615_ = leanh::lean_ctor_get(v___y_1602_, 12);
                v_suppressElabErrors_1616_ = leanh::lean_ctor_get_uint8(
                    v___y_1602_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1617_ = leanh::lean_ctor_get(v___y_1602_, 13);
                v_isSharedCheck_1631_ = (!leanh::lean_is_exclusive(v___y_1602_)) as u8;
                if v_isSharedCheck_1631_ == 0 {
                    v_unused_1632_ = leanh::lean_ctor_get(v___y_1602_, 4);
                    leanh::lean_dec(v_unused_1632_);
                    v_unused_1633_ = leanh::lean_ctor_get(v___y_1602_, 2);
                    leanh::lean_dec(v_unused_1633_);
                    v___x_1619_ = v___y_1602_;
                    v_isShared_1620_ = v_isSharedCheck_1631_;
                    state = 15;
                    continue;
                } else {
                    leanh::lean_inc(v_inheritedTraceOptions_1617_);
                    leanh::lean_inc(v_cancelTk_x3f_1615_);
                    leanh::lean_inc(v_currMacroScope_1614_);
                    leanh::lean_inc(v_quotContext_1613_);
                    leanh::lean_inc(v_maxHeartbeats_1612_);
                    leanh::lean_inc(v_initHeartbeats_1611_);
                    leanh::lean_inc(v_openDecls_1610_);
                    leanh::lean_inc(v_currNamespace_1609_);
                    leanh::lean_inc(v_ref_1608_);
                    leanh::lean_inc(v_currRecDepth_1607_);
                    leanh::lean_inc(v_fileMap_1606_);
                    leanh::lean_inc(v_fileName_1605_);
                    leanh::lean_dec(v___y_1602_);
                    v___x_1619_ = leanh::lean_box(0);
                    v_isShared_1620_ = v_isSharedCheck_1631_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_env_1621_ = leanh::lean_ctor_get(v___x_1604_, 0);
                leanh::lean_inc_ref(v_env_1621_);
                leanh::lean_dec(v___x_1604_);
                v___x_1622_ = l_Lean_maxRecDepth;
                v___x_1623_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(
                    v___y_1599_,
                    v___x_1622_,
                );
                leanh::lean_inc_ref(v___y_1599_);
                if v_isShared_1620_ == 0 {
                    leanh::lean_ctor_set(v___x_1619_, 4, v___x_1623_);
                    leanh::lean_ctor_set(v___x_1619_, 2, v___y_1599_);
                    v___x_1625_ = v___x_1619_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1630_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_fileName_1605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_fileMap_1606_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 2, v___y_1599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_currRecDepth_1607_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 4, v___x_1623_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 5, v_ref_1608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 6, v_currNamespace_1609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 7, v_openDecls_1610_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 8, v_initHeartbeats_1611_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 9, v_maxHeartbeats_1612_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 10, v_quotContext_1613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 11, v_currMacroScope_1614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 12, v_cancelTk_x3f_1615_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1630_,
                        13,
                        v_inheritedTraceOptions_1617_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1630_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1616_,
                    );
                    v___x_1625_ = v_reuseFailAlloc_1630_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1625_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_1596_,
                );
                v___x_1626_ = l_Lean_Compiler_compiler_postponeCompile;
                v___x_1627_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(
                    v___y_1599_,
                    v___x_1626_,
                    v___y_1598_,
                );
                v___x_1628_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(
                    v___x_1627_,
                    v___y_1593_,
                );
                v___x_1629_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1621_);
                leanh::lean_dec_ref(v_env_1621_);
                if v___x_1629_ == 0 {
                    if v___x_1628_ == 0 {
                        v___y_1515_ = v___x_1628_;
                        v___y_1516_ = v___y_1593_;
                        v___y_1517_ = v___y_1592_;
                        v___y_1518_ = v___y_1594_;
                        v___y_1519_ = v___y_1595_;
                        v___y_1520_ = v___y_1597_;
                        v___y_1521_ = v___y_1598_;
                        v___y_1522_ = v___x_1622_;
                        v___y_1523_ = v___y_1601_;
                        v___y_1524_ = v___y_1600_;
                        v___y_1525_ = v___x_1627_;
                        v___y_1526_ = v___x_1625_;
                        v___y_1527_ = v___y_1603_;
                        state = 8;
                        continue;
                    } else {
                        v___y_1558_ = v___x_1628_;
                        v___y_1559_ = v___x_1625_;
                        v___y_1560_ = v___y_1592_;
                        v___y_1561_ = v___y_1597_;
                        v___y_1562_ = v___x_1622_;
                        v___y_1563_ = v___y_1601_;
                        v___y_1564_ = v___y_1600_;
                        v___y_1565_ = v___x_1627_;
                        v___y_1566_ = v___y_1593_;
                        v___y_1567_ = v___y_1594_;
                        v___y_1568_ = v___y_1603_;
                        v___y_1569_ = v___y_1595_;
                        v___y_1570_ = v___y_1598_;
                        v___y_1571_ = v___x_1629_;
                        state = 11;
                        continue;
                    }
                } else {
                    v___y_1558_ = v___x_1628_;
                    v___y_1559_ = v___x_1625_;
                    v___y_1560_ = v___y_1592_;
                    v___y_1561_ = v___y_1597_;
                    v___y_1562_ = v___x_1622_;
                    v___y_1563_ = v___y_1601_;
                    v___y_1564_ = v___y_1600_;
                    v___y_1565_ = v___x_1627_;
                    v___y_1566_ = v___y_1593_;
                    v___y_1567_ = v___y_1594_;
                    v___y_1568_ = v___y_1603_;
                    v___y_1569_ = v___y_1595_;
                    v___y_1570_ = v___y_1598_;
                    v___y_1571_ = v___x_1628_;
                    state = 11;
                    continue;
                }
            }
            17 => {
                if v___y_1647_ == 0 {
                    v___x_1648_ = lean_st_ref_take(v___y_1640_);
                    v_env_1649_ = leanh::lean_ctor_get(v___x_1648_, 0);
                    v_nextMacroScope_1650_ = leanh::lean_ctor_get(v___x_1648_, 1);
                    v_ngen_1651_ = leanh::lean_ctor_get(v___x_1648_, 2);
                    v_auxDeclNGen_1652_ = leanh::lean_ctor_get(v___x_1648_, 3);
                    v_traceState_1653_ = leanh::lean_ctor_get(v___x_1648_, 4);
                    v_messages_1654_ = leanh::lean_ctor_get(v___x_1648_, 6);
                    v_infoState_1655_ = leanh::lean_ctor_get(v___x_1648_, 7);
                    v_snapshotTasks_1656_ = leanh::lean_ctor_get(v___x_1648_, 8);
                    v_isSharedCheck_1665_ = (!leanh::lean_is_exclusive(v___x_1648_)) as u8;
                    if v_isSharedCheck_1665_ == 0 {
                        v_unused_1666_ = leanh::lean_ctor_get(v___x_1648_, 5);
                        leanh::lean_dec(v_unused_1666_);
                        v___x_1658_ = v___x_1648_;
                        v_isShared_1659_ = v_isSharedCheck_1665_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_1656_);
                        leanh::lean_inc(v_infoState_1655_);
                        leanh::lean_inc(v_messages_1654_);
                        leanh::lean_inc(v_traceState_1653_);
                        leanh::lean_inc(v_auxDeclNGen_1652_);
                        leanh::lean_inc(v_ngen_1651_);
                        leanh::lean_inc(v_nextMacroScope_1650_);
                        leanh::lean_inc(v_env_1649_);
                        leanh::lean_dec(v___x_1648_);
                        v___x_1658_ = leanh::lean_box(0);
                        v_isShared_1659_ = v_isSharedCheck_1665_;
                        state = 18;
                        continue;
                    }
                } else {
                    v___y_1592_ = v___y_1635_;
                    v___y_1593_ = v___y_1641_;
                    v___y_1594_ = v___y_1642_;
                    v___y_1595_ = v___y_1644_;
                    v___y_1596_ = v___y_1643_;
                    v___y_1597_ = v___y_1636_;
                    v___y_1598_ = v___y_1645_;
                    v___y_1599_ = v___y_1637_;
                    v___y_1600_ = v___y_1638_;
                    v___y_1601_ = v___y_1639_;
                    v___y_1602_ = v___y_1646_;
                    v___y_1603_ = v___y_1640_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                v___x_1660_ = l_Lean_Kernel_enableDiag(v_env_1649_, v___y_1643_);
                leanh::lean_inc_ref(v___y_1636_);
                if v_isShared_1659_ == 0 {
                    leanh::lean_ctor_set(v___x_1658_, 5, v___y_1636_);
                    leanh::lean_ctor_set(v___x_1658_, 0, v___x_1660_);
                    v___x_1662_ = v___x_1658_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1664_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1660_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_nextMacroScope_1650_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_ngen_1651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_auxDeclNGen_1652_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_traceState_1653_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 5, v___y_1636_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 6, v_messages_1654_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 7, v_infoState_1655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 8, v_snapshotTasks_1656_);
                    v___x_1662_ = v_reuseFailAlloc_1664_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_1663_ = lean_st_ref_set(v___y_1640_, v___x_1662_);
                v___y_1592_ = v___y_1635_;
                v___y_1593_ = v___y_1641_;
                v___y_1594_ = v___y_1642_;
                v___y_1595_ = v___y_1644_;
                v___y_1596_ = v___y_1643_;
                v___y_1597_ = v___y_1636_;
                v___y_1598_ = v___y_1645_;
                v___y_1599_ = v___y_1637_;
                v___y_1600_ = v___y_1638_;
                v___y_1601_ = v___y_1639_;
                v___y_1602_ = v___y_1646_;
                v___y_1603_ = v___y_1640_;
                state = 14;
                continue;
            }
            20 => {
                leanh::lean_inc(v___y_1675_);
                leanh::lean_inc_ref(v___y_1674_);
                leanh::lean_inc(v___y_1673_);
                leanh::lean_inc_ref(v___y_1672_);
                leanh::lean_inc_ref(v___y_1671_);
                v___x_1676_ = lean_infer_type(
                    v___y_1671_,
                    v___y_1672_,
                    v___y_1673_,
                    v___y_1674_,
                    v___y_1675_,
                );
                if leanh::lean_obj_tag(v___x_1676_) == 0 {
                    v_a_1677_ = leanh::lean_ctor_get(v___x_1676_, 0);
                    leanh::lean_inc_n(v_a_1677_, 2);
                    leanh::lean_dec_ref_known(v___x_1676_, 1);
                    leanh::lean_inc(v___y_1675_);
                    leanh::lean_inc_ref(v___y_1674_);
                    leanh::lean_inc(v___y_1673_);
                    leanh::lean_inc_ref(v___y_1672_);
                    v___x_1678_ = leanh::lean_apply_6(
                        v_checkType_1412_,
                        v_a_1677_,
                        v___y_1672_,
                        v___y_1673_,
                        v___y_1674_,
                        v___y_1675_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1678_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1678_, 1);
                        v___x_1679_ = lean_st_ref_take(v___y_1675_);
                        v_env_1680_ = leanh::lean_ctor_get(v___x_1679_, 0);
                        v_nextMacroScope_1681_ = leanh::lean_ctor_get(v___x_1679_, 1);
                        v_ngen_1682_ = leanh::lean_ctor_get(v___x_1679_, 2);
                        v_auxDeclNGen_1683_ = leanh::lean_ctor_get(v___x_1679_, 3);
                        v_traceState_1684_ = leanh::lean_ctor_get(v___x_1679_, 4);
                        v_messages_1685_ = leanh::lean_ctor_get(v___x_1679_, 6);
                        v_infoState_1686_ = leanh::lean_ctor_get(v___x_1679_, 7);
                        v_snapshotTasks_1687_ = leanh::lean_ctor_get(v___x_1679_, 8);
                        v_isSharedCheck_1741_ =
                            (!leanh::lean_is_exclusive(v___x_1679_)) as u8;
                        if v_isSharedCheck_1741_ == 0 {
                            v_unused_1742_ = leanh::lean_ctor_get(v___x_1679_, 5);
                            leanh::lean_dec(v_unused_1742_);
                            v___x_1689_ = v___x_1679_;
                            v_isShared_1690_ = v_isSharedCheck_1741_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_1687_);
                            leanh::lean_inc(v_infoState_1686_);
                            leanh::lean_inc(v_messages_1685_);
                            leanh::lean_inc(v_traceState_1684_);
                            leanh::lean_inc(v_auxDeclNGen_1683_);
                            leanh::lean_inc(v_ngen_1682_);
                            leanh::lean_inc(v_nextMacroScope_1681_);
                            leanh::lean_inc(v_env_1680_);
                            leanh::lean_dec(v___x_1679_);
                            v___x_1689_ = leanh::lean_box(0);
                            v_isShared_1690_ = v_isSharedCheck_1741_;
                            state = 21;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1677_);
                        leanh::lean_dec(v___y_1675_);
                        leanh::lean_dec_ref(v___y_1674_);
                        leanh::lean_dec(v___y_1673_);
                        leanh::lean_dec_ref(v___y_1672_);
                        leanh::lean_dec_ref(v___y_1671_);
                        leanh::lean_dec(v___y_1670_);
                        leanh::lean_dec_ref(v___y_1668_);
                        v_a_1743_ = leanh::lean_ctor_get(v___x_1678_, 0);
                        v_isSharedCheck_1750_ =
                            (!leanh::lean_is_exclusive(v___x_1678_)) as u8;
                        if v_isSharedCheck_1750_ == 0 {
                            v___x_1745_ = v___x_1678_;
                            v_isShared_1746_ = v_isSharedCheck_1750_;
                            state = 27;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1743_);
                            leanh::lean_dec(v___x_1678_);
                            v___x_1745_ = leanh::lean_box(0);
                            v_isShared_1746_ = v_isSharedCheck_1750_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_1675_);
                    leanh::lean_dec_ref(v___y_1674_);
                    leanh::lean_dec(v___y_1673_);
                    leanh::lean_dec_ref(v___y_1672_);
                    leanh::lean_dec_ref(v___y_1671_);
                    leanh::lean_dec(v___y_1670_);
                    leanh::lean_dec_ref(v___y_1668_);
                    leanh::lean_dec_ref(v_checkType_1412_);
                    v_a_1751_ = leanh::lean_ctor_get(v___x_1676_, 0);
                    v_isSharedCheck_1758_ = (!leanh::lean_is_exclusive(v___x_1676_)) as u8;
                    if v_isSharedCheck_1758_ == 0 {
                        v___x_1753_ = v___x_1676_;
                        v_isShared_1754_ = v_isSharedCheck_1758_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1751_);
                        leanh::lean_dec(v___x_1676_);
                        v___x_1753_ = leanh::lean_box(0);
                        v_isShared_1754_ = v_isSharedCheck_1758_;
                        state = 29;
                        continue;
                    }
                }
            }
            21 => {
                v___x_1691_ = lean_array_to_list(v___y_1668_);
                leanh::lean_inc_n(v___y_1670_, 3);
                v___x_1692_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1692_, 0, v___y_1670_);
                leanh::lean_ctor_set(v___x_1692_, 1, v___x_1691_);
                leanh::lean_ctor_set(v___x_1692_, 2, v_a_1677_);
                leanh::lean_inc(v___y_1669_);
                v___x_1693_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1693_, 0, v___y_1670_);
                leanh::lean_ctor_set(v___x_1693_, 1, v___y_1669_);
                v___x_1694_ = l_Lean_markMeta(v_env_1680_, v___y_1670_);
                v___x_1695_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2,
                );
                if v_isShared_1690_ == 0 {
                    leanh::lean_ctor_set(v___x_1689_, 5, v___x_1695_);
                    leanh::lean_ctor_set(v___x_1689_, 0, v___x_1694_);
                    v___x_1697_ = v___x_1689_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1694_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_nextMacroScope_1681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_ngen_1682_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_auxDeclNGen_1683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_traceState_1684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 5, v___x_1695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 6, v_messages_1685_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 7, v_infoState_1686_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 8, v_snapshotTasks_1687_);
                    v___x_1697_ = v_reuseFailAlloc_1740_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1698_ = lean_st_ref_set(v___y_1675_, v___x_1697_);
                v___x_1699_ = lean_st_ref_take(v___y_1673_);
                v_mctx_1700_ = leanh::lean_ctor_get(v___x_1699_, 0);
                v_zetaDeltaFVarIds_1701_ = leanh::lean_ctor_get(v___x_1699_, 2);
                v_postponed_1702_ = leanh::lean_ctor_get(v___x_1699_, 3);
                v_diag_1703_ = leanh::lean_ctor_get(v___x_1699_, 4);
                v_isSharedCheck_1738_ = (!leanh::lean_is_exclusive(v___x_1699_)) as u8;
                if v_isSharedCheck_1738_ == 0 {
                    v_unused_1739_ = leanh::lean_ctor_get(v___x_1699_, 1);
                    leanh::lean_dec(v_unused_1739_);
                    v___x_1705_ = v___x_1699_;
                    v_isShared_1706_ = v_isSharedCheck_1738_;
                    state = 23;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1703_);
                    leanh::lean_inc(v_postponed_1702_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1701_);
                    leanh::lean_inc(v_mctx_1700_);
                    leanh::lean_dec(v___x_1699_);
                    v___x_1705_ = leanh::lean_box(0);
                    v_isShared_1706_ = v_isSharedCheck_1738_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_1707_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3,
                );
                if v_isShared_1706_ == 0 {
                    leanh::lean_ctor_set(v___x_1705_, 1, v___x_1707_);
                    v___x_1709_ = v___x_1705_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1737_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_mctx_1700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1707_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1737_,
                        2,
                        v_zetaDeltaFVarIds_1701_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_postponed_1702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_diag_1703_);
                    v___x_1709_ = v_reuseFailAlloc_1737_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_1710_ = lean_st_ref_set(v___y_1673_, v___x_1709_);
                v___x_1711_ = lean_st_ref_get(v___y_1675_);
                v_env_1712_ = leanh::lean_ctor_get(v___x_1711_, 0);
                leanh::lean_inc_ref(v_env_1712_);
                leanh::lean_dec(v___x_1711_);
                v_checked_1713_ = leanh::lean_ctor_get(v_env_1712_, 2);
                leanh::lean_inc_ref(v_checked_1713_);
                leanh::lean_dec_ref(v_env_1712_);
                v___x_1714_ = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4;
                v___x_1715_ = l_Lean_traceBlock___redArg(
                    v___x_1714_,
                    v_checked_1713_,
                    v___y_1674_,
                    v___y_1675_,
                );
                if leanh::lean_obj_tag(v___x_1715_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1715_, 1);
                    v___x_1716_ = lean_st_ref_get(v___y_1675_);
                    v_options_1717_ = leanh::lean_ctor_get(v___y_1674_, 2);
                    v_env_1718_ = leanh::lean_ctor_get(v___x_1716_, 0);
                    leanh::lean_inc_ref(v_env_1718_);
                    leanh::lean_dec(v___x_1716_);
                    v___x_1719_ = leanh::lean_box(0);
                    v___x_1720_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v___x_1720_, 0, v___x_1692_);
                    leanh::lean_ctor_set(v___x_1720_, 1, v___y_1671_);
                    leanh::lean_ctor_set(v___x_1720_, 2, v___x_1719_);
                    leanh::lean_ctor_set(v___x_1720_, 3, v___x_1693_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1720_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v_safety_1413_,
                    );
                    v___x_1721_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1721_, 0, v___x_1720_);
                    v___x_1722_ = 1;
                    v___x_1723_ = 0;
                    v___x_1724_ = l_Lean_Elab_async;
                    leanh::lean_inc_ref(v_options_1717_);
                    v___x_1725_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(
                        v_options_1717_,
                        v___x_1724_,
                        v___x_1723_,
                    );
                    v___x_1726_ = l_Lean_diagnostics;
                    v___x_1727_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(
                        v___x_1725_,
                        v___x_1726_,
                    );
                    v___x_1728_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1718_);
                    leanh::lean_dec_ref(v_env_1718_);
                    if v___x_1728_ == 0 {
                        if v___x_1727_ == 0 {
                            v___y_1592_ = v___x_1722_;
                            v___y_1593_ = v___x_1726_;
                            v___y_1594_ = v___x_1721_;
                            v___y_1595_ = v___y_1672_;
                            v___y_1596_ = v___x_1727_;
                            v___y_1597_ = v___x_1695_;
                            v___y_1598_ = v___x_1723_;
                            v___y_1599_ = v___x_1725_;
                            v___y_1600_ = v___y_1673_;
                            v___y_1601_ = v___y_1670_;
                            v___y_1602_ = v___y_1674_;
                            v___y_1603_ = v___y_1675_;
                            state = 14;
                            continue;
                        } else {
                            v___y_1635_ = v___x_1722_;
                            v___y_1636_ = v___x_1695_;
                            v___y_1637_ = v___x_1725_;
                            v___y_1638_ = v___y_1673_;
                            v___y_1639_ = v___y_1670_;
                            v___y_1640_ = v___y_1675_;
                            v___y_1641_ = v___x_1726_;
                            v___y_1642_ = v___x_1721_;
                            v___y_1643_ = v___x_1727_;
                            v___y_1644_ = v___y_1672_;
                            v___y_1645_ = v___x_1723_;
                            v___y_1646_ = v___y_1674_;
                            v___y_1647_ = v___x_1728_;
                            state = 17;
                            continue;
                        }
                    } else {
                        v___y_1635_ = v___x_1722_;
                        v___y_1636_ = v___x_1695_;
                        v___y_1637_ = v___x_1725_;
                        v___y_1638_ = v___y_1673_;
                        v___y_1639_ = v___y_1670_;
                        v___y_1640_ = v___y_1675_;
                        v___y_1641_ = v___x_1726_;
                        v___y_1642_ = v___x_1721_;
                        v___y_1643_ = v___x_1727_;
                        v___y_1644_ = v___y_1672_;
                        v___y_1645_ = v___x_1723_;
                        v___y_1646_ = v___y_1674_;
                        v___y_1647_ = v___x_1727_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_1693_, 2);
                    leanh::lean_dec_ref_known(v___x_1692_, 3);
                    leanh::lean_dec(v___y_1675_);
                    leanh::lean_dec_ref(v___y_1674_);
                    leanh::lean_dec(v___y_1673_);
                    leanh::lean_dec_ref(v___y_1672_);
                    leanh::lean_dec_ref(v___y_1671_);
                    leanh::lean_dec(v___y_1670_);
                    v_a_1729_ = leanh::lean_ctor_get(v___x_1715_, 0);
                    v_isSharedCheck_1736_ = (!leanh::lean_is_exclusive(v___x_1715_)) as u8;
                    if v_isSharedCheck_1736_ == 0 {
                        v___x_1731_ = v___x_1715_;
                        v_isShared_1732_ = v_isSharedCheck_1736_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1729_);
                        leanh::lean_dec(v___x_1715_);
                        v___x_1731_ = leanh::lean_box(0);
                        v_isShared_1732_ = v_isSharedCheck_1736_;
                        state = 25;
                        continue;
                    }
                }
            }
            25 => {
                if v_isShared_1732_ == 0 {
                    v___x_1734_ = v___x_1731_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
                    v___x_1734_ = v_reuseFailAlloc_1735_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1734_;
            }
            27 => {
                if v_isShared_1746_ == 0 {
                    v___x_1748_ = v___x_1745_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
                    v___x_1748_ = v_reuseFailAlloc_1749_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1748_;
            }
            29 => {
                if v_isShared_1754_ == 0 {
                    v___x_1756_ = v___x_1753_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
                    v___x_1756_ = v_reuseFailAlloc_1757_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_1756_;
            }
            31 => {
                v___x_1764_ = lean_st_ref_get(v___y_1763_);
                v___x_1765_ = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6;
                v___x_1766_ = l_Lean_Core_mkFreshUserName(v___x_1765_, v___y_1762_, v___y_1763_);
                if leanh::lean_obj_tag(v___x_1766_) == 0 {
                    v_a_1767_ = leanh::lean_ctor_get(v___x_1766_, 0);
                    leanh::lean_inc(v_a_1767_);
                    leanh::lean_dec_ref_known(v___x_1766_, 1);
                    v___x_1768_ =
                        l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(
                            v_value_1414_,
                            v___y_1761_,
                        );
                    if leanh::lean_obj_tag(v___x_1768_) == 0 {
                        v_a_1769_ = leanh::lean_ctor_get(v___x_1768_, 0);
                        leanh::lean_inc_n(v_a_1769_, 2);
                        leanh::lean_dec_ref_known(v___x_1768_, 1);
                        v_env_1770_ = leanh::lean_ctor_get(v___x_1764_, 0);
                        leanh::lean_inc_ref(v_env_1770_);
                        leanh::lean_dec(v___x_1764_);
                        v___x_1771_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once
                            ),
                            _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10,
                        );
                        v___x_1772_ = l_Lean_collectLevelParams(v___x_1771_, v_a_1769_);
                        v_params_1773_ = leanh::lean_ctor_get(v___x_1772_, 2);
                        leanh::lean_inc_ref(v_params_1773_);
                        leanh::lean_dec_ref(v___x_1772_);
                        v___x_1774_ = l_Lean_mkPrivateName(v_env_1770_, v_a_1767_);
                        leanh::lean_dec_ref(v_env_1770_);
                        v___x_1775_ = leanh::lean_box(0);
                        v___x_1776_ = l_Lean_Expr_hasMVar(v_a_1769_);
                        if v___x_1776_ == 0 {
                            v___y_1668_ = v_params_1773_;
                            v___y_1669_ = v___x_1775_;
                            v___y_1670_ = v___x_1774_;
                            v___y_1671_ = v_a_1769_;
                            v___y_1672_ = v___y_1760_;
                            v___y_1673_ = v___y_1761_;
                            v___y_1674_ = v___y_1762_;
                            v___y_1675_ = v___y_1763_;
                            state = 20;
                            continue;
                        } else {
                            v___x_1777_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once
                                ),
                                _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12,
                            );
                            leanh::lean_inc(v_a_1769_);
                            v___x_1778_ = l_Lean_indentExpr(v_a_1769_);
                            v___x_1779_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1779_, 0, v___x_1777_);
                            leanh::lean_ctor_set(v___x_1779_, 1, v___x_1778_);
                            v___x_1780_ =
                                l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(
                                    v___x_1779_,
                                    v___y_1760_,
                                    v___y_1761_,
                                    v___y_1762_,
                                    v___y_1763_,
                                );
                            if leanh::lean_obj_tag(v___x_1780_) == 0 {
                                leanh::lean_dec_ref_known(v___x_1780_, 1);
                                v___y_1668_ = v_params_1773_;
                                v___y_1669_ = v___x_1775_;
                                v___y_1670_ = v___x_1774_;
                                v___y_1671_ = v_a_1769_;
                                v___y_1672_ = v___y_1760_;
                                v___y_1673_ = v___y_1761_;
                                v___y_1674_ = v___y_1762_;
                                v___y_1675_ = v___y_1763_;
                                state = 20;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1774_);
                                leanh::lean_dec_ref(v_params_1773_);
                                leanh::lean_dec(v_a_1769_);
                                leanh::lean_dec(v___y_1763_);
                                leanh::lean_dec_ref(v___y_1762_);
                                leanh::lean_dec(v___y_1761_);
                                leanh::lean_dec_ref(v___y_1760_);
                                leanh::lean_dec_ref(v_checkType_1412_);
                                v_a_1781_ = leanh::lean_ctor_get(v___x_1780_, 0);
                                v_isSharedCheck_1788_ =
                                    (!leanh::lean_is_exclusive(v___x_1780_)) as u8;
                                if v_isSharedCheck_1788_ == 0 {
                                    v___x_1783_ = v___x_1780_;
                                    v_isShared_1784_ = v_isSharedCheck_1788_;
                                    state = 32;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1781_);
                                    leanh::lean_dec(v___x_1780_);
                                    v___x_1783_ = leanh::lean_box(0);
                                    v_isShared_1784_ = v_isSharedCheck_1788_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1767_);
                        leanh::lean_dec(v___x_1764_);
                        leanh::lean_dec(v___y_1763_);
                        leanh::lean_dec_ref(v___y_1762_);
                        leanh::lean_dec(v___y_1761_);
                        leanh::lean_dec_ref(v___y_1760_);
                        leanh::lean_dec_ref(v_checkType_1412_);
                        v_a_1789_ = leanh::lean_ctor_get(v___x_1768_, 0);
                        v_isSharedCheck_1796_ =
                            (!leanh::lean_is_exclusive(v___x_1768_)) as u8;
                        if v_isSharedCheck_1796_ == 0 {
                            v___x_1791_ = v___x_1768_;
                            v_isShared_1792_ = v_isSharedCheck_1796_;
                            state = 34;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1789_);
                            leanh::lean_dec(v___x_1768_);
                            v___x_1791_ = leanh::lean_box(0);
                            v_isShared_1792_ = v_isSharedCheck_1796_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1764_);
                    leanh::lean_dec(v___y_1763_);
                    leanh::lean_dec_ref(v___y_1762_);
                    leanh::lean_dec(v___y_1761_);
                    leanh::lean_dec_ref(v___y_1760_);
                    leanh::lean_dec_ref(v_value_1414_);
                    leanh::lean_dec_ref(v_checkType_1412_);
                    v_a_1797_ = leanh::lean_ctor_get(v___x_1766_, 0);
                    v_isSharedCheck_1804_ = (!leanh::lean_is_exclusive(v___x_1766_)) as u8;
                    if v_isSharedCheck_1804_ == 0 {
                        v___x_1799_ = v___x_1766_;
                        v_isShared_1800_ = v_isSharedCheck_1804_;
                        state = 36;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1797_);
                        leanh::lean_dec(v___x_1766_);
                        v___x_1799_ = leanh::lean_box(0);
                        v_isShared_1800_ = v_isSharedCheck_1804_;
                        state = 36;
                        continue;
                    }
                }
            }
            32 => {
                if v_isShared_1784_ == 0 {
                    v___x_1786_ = v___x_1783_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1787_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
                    v___x_1786_ = v_reuseFailAlloc_1787_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1786_;
            }
            34 => {
                if v_isShared_1792_ == 0 {
                    v___x_1794_ = v___x_1791_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1795_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
                    v___x_1794_ = v_reuseFailAlloc_1795_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_1794_;
            }
            36 => {
                if v_isShared_1800_ == 0 {
                    v___x_1802_ = v___x_1799_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1803_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
                    v___x_1802_ = v_reuseFailAlloc_1803_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1802_;
            }
            38 => {
                v___x_1814_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2,
                );
                v___x_1815_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                leanh::lean_ctor_set(v___x_1815_, 0, v___y_1813_);
                leanh::lean_ctor_set(v___x_1815_, 1, v_nextMacroScope_1806_);
                leanh::lean_ctor_set(v___x_1815_, 2, v_ngen_1807_);
                leanh::lean_ctor_set(v___x_1815_, 3, v_auxDeclNGen_1808_);
                leanh::lean_ctor_set(v___x_1815_, 4, v_traceState_1809_);
                leanh::lean_ctor_set(v___x_1815_, 5, v___x_1814_);
                leanh::lean_ctor_set(v___x_1815_, 6, v_messages_1810_);
                leanh::lean_ctor_set(v___x_1815_, 7, v_infoState_1811_);
                leanh::lean_ctor_set(v___x_1815_, 8, v_snapshotTasks_1812_);
                v___x_1816_ = lean_st_ref_set(v___y_1418_, v___x_1815_);
                v___x_1817_ = lean_st_ref_take(v___y_1416_);
                v_mctx_1818_ = leanh::lean_ctor_get(v___x_1817_, 0);
                v_zetaDeltaFVarIds_1819_ = leanh::lean_ctor_get(v___x_1817_, 2);
                v_postponed_1820_ = leanh::lean_ctor_get(v___x_1817_, 3);
                v_diag_1821_ = leanh::lean_ctor_get(v___x_1817_, 4);
                v_isSharedCheck_1830_ = (!leanh::lean_is_exclusive(v___x_1817_)) as u8;
                if v_isSharedCheck_1830_ == 0 {
                    v_unused_1831_ = leanh::lean_ctor_get(v___x_1817_, 1);
                    leanh::lean_dec(v_unused_1831_);
                    v___x_1823_ = v___x_1817_;
                    v_isShared_1824_ = v_isSharedCheck_1830_;
                    state = 39;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1821_);
                    leanh::lean_inc(v_postponed_1820_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1819_);
                    leanh::lean_inc(v_mctx_1818_);
                    leanh::lean_dec(v___x_1817_);
                    v___x_1823_ = leanh::lean_box(0);
                    v_isShared_1824_ = v_isSharedCheck_1830_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                v___x_1825_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3,
                );
                if v_isShared_1824_ == 0 {
                    leanh::lean_ctor_set(v___x_1823_, 1, v___x_1825_);
                    v___x_1827_ = v___x_1823_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1829_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_mctx_1818_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___x_1825_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1829_,
                        2,
                        v_zetaDeltaFVarIds_1819_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_postponed_1820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_diag_1821_);
                    v___x_1827_ = v_reuseFailAlloc_1829_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v___x_1828_ = lean_st_ref_set(v___y_1416_, v___x_1827_);
                v___y_1760_ = v___y_1415_;
                v___y_1761_ = v___y_1416_;
                v___y_1762_ = v___y_1417_;
                v___y_1763_ = v___y_1418_;
                state = 31;
                continue;
            }
            41 => {
                v___x_1834_ = lean_st_ref_take(v___y_1418_);
                v_env_1835_ = leanh::lean_ctor_get(v___x_1834_, 0);
                leanh::lean_inc_ref_n(v_env_1835_, 2);
                v_nextMacroScope_1836_ = leanh::lean_ctor_get(v___x_1834_, 1);
                leanh::lean_inc(v_nextMacroScope_1836_);
                v_ngen_1837_ = leanh::lean_ctor_get(v___x_1834_, 2);
                leanh::lean_inc_ref(v_ngen_1837_);
                v_auxDeclNGen_1838_ = leanh::lean_ctor_get(v___x_1834_, 3);
                leanh::lean_inc_ref(v_auxDeclNGen_1838_);
                v_traceState_1839_ = leanh::lean_ctor_get(v___x_1834_, 4);
                leanh::lean_inc_ref(v_traceState_1839_);
                v_messages_1840_ = leanh::lean_ctor_get(v___x_1834_, 6);
                leanh::lean_inc_ref(v_messages_1840_);
                v_infoState_1841_ = leanh::lean_ctor_get(v___x_1834_, 7);
                leanh::lean_inc_ref(v_infoState_1841_);
                v_snapshotTasks_1842_ = leanh::lean_ctor_get(v___x_1834_, 8);
                leanh::lean_inc_ref(v_snapshotTasks_1842_);
                leanh::lean_dec(v___x_1834_);
                v___x_1843_ = l_Lean_Environment_importEnv_x3f(v_env_1835_);
                if leanh::lean_obj_tag(v___x_1843_) == 0 {
                    v_nextMacroScope_1806_ = v_nextMacroScope_1836_;
                    v_ngen_1807_ = v_ngen_1837_;
                    v_auxDeclNGen_1808_ = v_auxDeclNGen_1838_;
                    v_traceState_1809_ = v_traceState_1839_;
                    v_messages_1810_ = v_messages_1840_;
                    v_infoState_1811_ = v_infoState_1841_;
                    v_snapshotTasks_1812_ = v_snapshotTasks_1842_;
                    v___y_1813_ = v_env_1835_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_1835_);
                    v_val_1844_ = leanh::lean_ctor_get(v___x_1843_, 0);
                    leanh::lean_inc(v_val_1844_);
                    leanh::lean_dec_ref_known(v___x_1843_, 1);
                    v_nextMacroScope_1806_ = v_nextMacroScope_1836_;
                    v_ngen_1807_ = v_ngen_1837_;
                    v_auxDeclNGen_1808_ = v_auxDeclNGen_1838_;
                    v_traceState_1809_ = v_traceState_1839_;
                    v_messages_1810_ = v_messages_1840_;
                    v_infoState_1811_ = v_infoState_1841_;
                    v_snapshotTasks_1812_ = v_snapshotTasks_1842_;
                    v___y_1813_ = v_val_1844_;
                    state = 38;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(
    mut v_checkMeta_1853_: *mut leanh::LeanObject,
    mut v_checkType_1854_: *mut leanh::LeanObject,
    mut v_safety_1855_: *mut leanh::LeanObject,
    mut v_value_1856_: *mut leanh::LeanObject,
    mut v___y_1857_: *mut leanh::LeanObject,
    mut v___y_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
    mut v___y_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_1862_: u8 = 0;
    let mut v_safety_boxed_1863_: u8 = 0;
    let mut v_res_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1862_ = (leanh::lean_unbox(v_checkMeta_1853_) as u8);
    v_safety_boxed_1863_ = (leanh::lean_unbox(v_safety_1855_) as u8);
    v_res_1864_ = l_Lean_Meta_evalExprCore___redArg___lam__0(
        v_checkMeta_boxed_1862_,
        v_checkType_1854_,
        v_safety_boxed_1863_,
        v_value_1856_,
        v___y_1857_,
        v___y_1858_,
        v___y_1859_,
        v___y_1860_,
    );
    return v_res_1864_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(
    mut v_env_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1879_: u8 = 0;
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut v_unused_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1902_: u8 = 0;
    let mut v_unused_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1869_ = lean_st_ref_take(v___y_1867_);
                v_nextMacroScope_1870_ = leanh::lean_ctor_get(v___x_1869_, 1);
                v_ngen_1871_ = leanh::lean_ctor_get(v___x_1869_, 2);
                v_auxDeclNGen_1872_ = leanh::lean_ctor_get(v___x_1869_, 3);
                v_traceState_1873_ = leanh::lean_ctor_get(v___x_1869_, 4);
                v_messages_1874_ = leanh::lean_ctor_get(v___x_1869_, 6);
                v_infoState_1875_ = leanh::lean_ctor_get(v___x_1869_, 7);
                v_snapshotTasks_1876_ = leanh::lean_ctor_get(v___x_1869_, 8);
                v_isSharedCheck_1902_ = (!leanh::lean_is_exclusive(v___x_1869_)) as u8;
                if v_isSharedCheck_1902_ == 0 {
                    v_unused_1903_ = leanh::lean_ctor_get(v___x_1869_, 5);
                    leanh::lean_dec(v_unused_1903_);
                    v_unused_1904_ = leanh::lean_ctor_get(v___x_1869_, 0);
                    leanh::lean_dec(v_unused_1904_);
                    v___x_1878_ = v___x_1869_;
                    v_isShared_1879_ = v_isSharedCheck_1902_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1876_);
                    leanh::lean_inc(v_infoState_1875_);
                    leanh::lean_inc(v_messages_1874_);
                    leanh::lean_inc(v_traceState_1873_);
                    leanh::lean_inc(v_auxDeclNGen_1872_);
                    leanh::lean_inc(v_ngen_1871_);
                    leanh::lean_inc(v_nextMacroScope_1870_);
                    leanh::lean_dec(v___x_1869_);
                    v___x_1878_ = leanh::lean_box(0);
                    v_isShared_1879_ = v_isSharedCheck_1902_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1880_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2,
                );
                if v_isShared_1879_ == 0 {
                    leanh::lean_ctor_set(v___x_1878_, 5, v___x_1880_);
                    leanh::lean_ctor_set(v___x_1878_, 0, v_env_1865_);
                    v___x_1882_ = v___x_1878_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1901_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_env_1865_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_nextMacroScope_1870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_ngen_1871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_auxDeclNGen_1872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_traceState_1873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 5, v___x_1880_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 6, v_messages_1874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 7, v_infoState_1875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 8, v_snapshotTasks_1876_);
                    v___x_1882_ = v_reuseFailAlloc_1901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1883_ = lean_st_ref_set(v___y_1867_, v___x_1882_);
                v___x_1884_ = lean_st_ref_take(v___y_1866_);
                v_mctx_1885_ = leanh::lean_ctor_get(v___x_1884_, 0);
                v_zetaDeltaFVarIds_1886_ = leanh::lean_ctor_get(v___x_1884_, 2);
                v_postponed_1887_ = leanh::lean_ctor_get(v___x_1884_, 3);
                v_diag_1888_ = leanh::lean_ctor_get(v___x_1884_, 4);
                v_isSharedCheck_1899_ = (!leanh::lean_is_exclusive(v___x_1884_)) as u8;
                if v_isSharedCheck_1899_ == 0 {
                    v_unused_1900_ = leanh::lean_ctor_get(v___x_1884_, 1);
                    leanh::lean_dec(v_unused_1900_);
                    v___x_1890_ = v___x_1884_;
                    v_isShared_1891_ = v_isSharedCheck_1899_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1888_);
                    leanh::lean_inc(v_postponed_1887_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1886_);
                    leanh::lean_inc(v_mctx_1885_);
                    leanh::lean_dec(v___x_1884_);
                    v___x_1890_ = leanh::lean_box(0);
                    v_isShared_1891_ = v_isSharedCheck_1899_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1892_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3,
                );
                if v_isShared_1891_ == 0 {
                    leanh::lean_ctor_set(v___x_1890_, 1, v___x_1892_);
                    v___x_1894_ = v___x_1890_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1898_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_mctx_1885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1892_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1898_,
                        2,
                        v_zetaDeltaFVarIds_1886_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_postponed_1887_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 4, v_diag_1888_);
                    v___x_1894_ = v_reuseFailAlloc_1898_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1895_ = lean_st_ref_set(v___y_1866_, v___x_1894_);
                v___x_1896_ = leanh::lean_box(0);
                v___x_1897_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1897_, 0, v___x_1896_);
                return v___x_1897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(
    mut v_env_1905_: *mut leanh::LeanObject,
    mut v___y_1906_: *mut leanh::LeanObject,
    mut v___y_1907_: *mut leanh::LeanObject,
    mut v___y_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_1905_, v___y_1906_, v___y_1907_);
    leanh::lean_dec(v___y_1907_);
    leanh::lean_dec(v___y_1906_);
    return v_res_1909_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(
    mut v_env_1910_: *mut leanh::LeanObject,
    mut v_x_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
    mut v___y_1913_: *mut leanh::LeanObject,
    mut v___y_1914_: *mut leanh::LeanObject,
    mut v___y_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut v_unused_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v_unused_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1917_ = lean_st_ref_get(v___y_1915_);
                v_env_1918_ = leanh::lean_ctor_get(v___x_1917_, 0);
                leanh::lean_inc_ref(v_env_1918_);
                leanh::lean_dec(v___x_1917_);
                v___x_1930_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_1910_, v___y_1913_, v___y_1915_);
                leanh::lean_dec_ref(v___x_1930_);
                leanh::lean_inc(v___y_1915_);
                leanh::lean_inc_ref(v___y_1914_);
                leanh::lean_inc(v___y_1913_);
                leanh::lean_inc_ref(v___y_1912_);
                v___x_1931_ = leanh::lean_apply_5(
                    v_x_1911_,
                    v___y_1912_,
                    v___y_1913_,
                    v___y_1914_,
                    v___y_1915_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1931_) == 0 {
                    v_a_1932_ = leanh::lean_ctor_get(v___x_1931_, 0);
                    leanh::lean_inc(v_a_1932_);
                    leanh::lean_dec_ref_known(v___x_1931_, 1);
                    v___x_1933_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_1918_, v___y_1913_, v___y_1915_);
                    v_isSharedCheck_1940_ = (!leanh::lean_is_exclusive(v___x_1933_)) as u8;
                    if v_isSharedCheck_1940_ == 0 {
                        v_unused_1941_ = leanh::lean_ctor_get(v___x_1933_, 0);
                        leanh::lean_dec(v_unused_1941_);
                        v___x_1935_ = v___x_1933_;
                        v_isShared_1936_ = v_isSharedCheck_1940_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1933_);
                        v___x_1935_ = leanh::lean_box(0);
                        v_isShared_1936_ = v_isSharedCheck_1940_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_1942_ = leanh::lean_ctor_get(v___x_1931_, 0);
                    leanh::lean_inc(v_a_1942_);
                    leanh::lean_dec_ref_known(v___x_1931_, 1);
                    v_a_1920_ = v_a_1942_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1921_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_1918_, v___y_1913_, v___y_1915_);
                v_isSharedCheck_1928_ = (!leanh::lean_is_exclusive(v___x_1921_)) as u8;
                if v_isSharedCheck_1928_ == 0 {
                    v_unused_1929_ = leanh::lean_ctor_get(v___x_1921_, 0);
                    leanh::lean_dec(v_unused_1929_);
                    v___x_1923_ = v___x_1921_;
                    v_isShared_1924_ = v_isSharedCheck_1928_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1921_);
                    v___x_1923_ = leanh::lean_box(0);
                    v_isShared_1924_ = v_isSharedCheck_1928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1924_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1923_, 1);
                    leanh::lean_ctor_set(v___x_1923_, 0, v_a_1920_);
                    v___x_1926_ = v___x_1923_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1927_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1920_);
                    v___x_1926_ = v_reuseFailAlloc_1927_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1926_;
            }
            4 => {
                if v_isShared_1936_ == 0 {
                    leanh::lean_ctor_set(v___x_1935_, 0, v_a_1932_);
                    v___x_1938_ = v___x_1935_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1932_);
                    v___x_1938_ = v_reuseFailAlloc_1939_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(
    mut v_env_1943_: *mut leanh::LeanObject,
    mut v_x_1944_: *mut leanh::LeanObject,
    mut v___y_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
    mut v___y_1947_: *mut leanh::LeanObject,
    mut v___y_1948_: *mut leanh::LeanObject,
    mut v___y_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(
        v_env_1943_,
        v_x_1944_,
        v___y_1945_,
        v___y_1946_,
        v___y_1947_,
        v___y_1948_,
    );
    leanh::lean_dec(v___y_1948_);
    leanh::lean_dec_ref(v___y_1947_);
    leanh::lean_dec(v___y_1946_);
    leanh::lean_dec_ref(v___y_1945_);
    return v_res_1950_;
}
pub unsafe fn l_Lean_Meta_evalExprCore___redArg(
    mut v_value_1951_: *mut leanh::LeanObject,
    mut v_checkType_1952_: *mut leanh::LeanObject,
    mut v_safety_1953_: u8,
    mut v_checkMeta_1954_: u8,
    mut v_a_1955_: *mut leanh::LeanObject,
    mut v_a_1956_: *mut leanh::LeanObject,
    mut v_a_1957_: *mut leanh::LeanObject,
    mut v_a_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = lean_st_ref_get(v_a_1958_);
    v_env_1961_ = leanh::lean_ctor_get(v___x_1960_, 0);
    leanh::lean_inc_ref(v_env_1961_);
    leanh::lean_dec(v___x_1960_);
    v___x_1962_ = leanh::lean_box((v_checkMeta_1954_) as usize);
    v___x_1963_ = leanh::lean_box((v_safety_1953_) as usize);
    v___f_1964_ = leanh::lean_alloc_closure(
        l_Lean_Meta_evalExprCore___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_1964_, 0, v___x_1962_);
    leanh::lean_closure_set(v___f_1964_, 1, v_checkType_1952_);
    leanh::lean_closure_set(v___f_1964_, 2, v___x_1963_);
    leanh::lean_closure_set(v___f_1964_, 3, v_value_1951_);
    v___x_1965_ = l_Lean_Environment_unlockAsync(v_env_1961_);
    v___x_1966_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(
        v___x_1965_,
        v___f_1964_,
        v_a_1955_,
        v_a_1956_,
        v_a_1957_,
        v_a_1958_,
    );
    return v___x_1966_;
}
pub unsafe fn l_Lean_Meta_evalExprCore___redArg___boxed(
    mut v_value_1967_: *mut leanh::LeanObject,
    mut v_checkType_1968_: *mut leanh::LeanObject,
    mut v_safety_1969_: *mut leanh::LeanObject,
    mut v_checkMeta_1970_: *mut leanh::LeanObject,
    mut v_a_1971_: *mut leanh::LeanObject,
    mut v_a_1972_: *mut leanh::LeanObject,
    mut v_a_1973_: *mut leanh::LeanObject,
    mut v_a_1974_: *mut leanh::LeanObject,
    mut v_a_1975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_safety_boxed_1976_: u8 = 0;
    let mut v_checkMeta_boxed_1977_: u8 = 0;
    let mut v_res_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_safety_boxed_1976_ = (leanh::lean_unbox(v_safety_1969_) as u8);
    v_checkMeta_boxed_1977_ = (leanh::lean_unbox(v_checkMeta_1970_) as u8);
    v_res_1978_ = l_Lean_Meta_evalExprCore___redArg(
        v_value_1967_,
        v_checkType_1968_,
        v_safety_boxed_1976_,
        v_checkMeta_boxed_1977_,
        v_a_1971_,
        v_a_1972_,
        v_a_1973_,
        v_a_1974_,
    );
    leanh::lean_dec(v_a_1974_);
    leanh::lean_dec_ref(v_a_1973_);
    leanh::lean_dec(v_a_1972_);
    leanh::lean_dec_ref(v_a_1971_);
    return v_res_1978_;
}
pub unsafe fn l_Lean_Meta_evalExprCore(
    mut v_00_u03b1_1979_: *mut leanh::LeanObject,
    mut v_value_1980_: *mut leanh::LeanObject,
    mut v_checkType_1981_: *mut leanh::LeanObject,
    mut v_safety_1982_: u8,
    mut v_checkMeta_1983_: u8,
    mut v_a_1984_: *mut leanh::LeanObject,
    mut v_a_1985_: *mut leanh::LeanObject,
    mut v_a_1986_: *mut leanh::LeanObject,
    mut v_a_1987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1989_ = l_Lean_Meta_evalExprCore___redArg(
        v_value_1980_,
        v_checkType_1981_,
        v_safety_1982_,
        v_checkMeta_1983_,
        v_a_1984_,
        v_a_1985_,
        v_a_1986_,
        v_a_1987_,
    );
    return v___x_1989_;
}
pub unsafe fn l_Lean_Meta_evalExprCore___boxed(
    mut v_00_u03b1_1990_: *mut leanh::LeanObject,
    mut v_value_1991_: *mut leanh::LeanObject,
    mut v_checkType_1992_: *mut leanh::LeanObject,
    mut v_safety_1993_: *mut leanh::LeanObject,
    mut v_checkMeta_1994_: *mut leanh::LeanObject,
    mut v_a_1995_: *mut leanh::LeanObject,
    mut v_a_1996_: *mut leanh::LeanObject,
    mut v_a_1997_: *mut leanh::LeanObject,
    mut v_a_1998_: *mut leanh::LeanObject,
    mut v_a_1999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_safety_boxed_2000_: u8 = 0;
    let mut v_checkMeta_boxed_2001_: u8 = 0;
    let mut v_res_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_safety_boxed_2000_ = (leanh::lean_unbox(v_safety_1993_) as u8);
    v_checkMeta_boxed_2001_ = (leanh::lean_unbox(v_checkMeta_1994_) as u8);
    v_res_2002_ = l_Lean_Meta_evalExprCore(
        v_00_u03b1_1990_,
        v_value_1991_,
        v_checkType_1992_,
        v_safety_boxed_2000_,
        v_checkMeta_boxed_2001_,
        v_a_1995_,
        v_a_1996_,
        v_a_1997_,
        v_a_1998_,
    );
    leanh::lean_dec(v_a_1998_);
    leanh::lean_dec_ref(v_a_1997_);
    leanh::lean_dec(v_a_1996_);
    leanh::lean_dec_ref(v_a_1995_);
    return v_res_2002_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(
    mut v_00_u03b1_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
    mut v___y_2006_: *mut leanh::LeanObject,
    mut v___y_2007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2009_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
    return v___x_2009_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(
    mut v_00_u03b1_2010_: *mut leanh::LeanObject,
    mut v___y_2011_: *mut leanh::LeanObject,
    mut v___y_2012_: *mut leanh::LeanObject,
    mut v___y_2013_: *mut leanh::LeanObject,
    mut v___y_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2016_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
    leanh::lean_dec(v___y_2014_);
    leanh::lean_dec_ref(v___y_2013_);
    leanh::lean_dec(v___y_2012_);
    leanh::lean_dec_ref(v___y_2011_);
    return v_res_2016_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(
    mut v_00_u03b1_2017_: *mut leanh::LeanObject,
    mut v_constName_2018_: *mut leanh::LeanObject,
    mut v_checkMeta_2019_: u8,
    mut v___y_2020_: *mut leanh::LeanObject,
    mut v___y_2021_: *mut leanh::LeanObject,
    mut v___y_2022_: *mut leanh::LeanObject,
    mut v___y_2023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2025_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(
        v_constName_2018_,
        v_checkMeta_2019_,
        v___y_2020_,
        v___y_2021_,
        v___y_2022_,
        v___y_2023_,
    );
    return v___x_2025_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(
    mut v_00_u03b1_2026_: *mut leanh::LeanObject,
    mut v_constName_2027_: *mut leanh::LeanObject,
    mut v_checkMeta_2028_: *mut leanh::LeanObject,
    mut v___y_2029_: *mut leanh::LeanObject,
    mut v___y_2030_: *mut leanh::LeanObject,
    mut v___y_2031_: *mut leanh::LeanObject,
    mut v___y_2032_: *mut leanh::LeanObject,
    mut v___y_2033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_2034_: u8 = 0;
    let mut v_res_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2034_ = (leanh::lean_unbox(v_checkMeta_2028_) as u8);
    v_res_2035_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(
        v_00_u03b1_2026_,
        v_constName_2027_,
        v_checkMeta_boxed_2034_,
        v___y_2029_,
        v___y_2030_,
        v___y_2031_,
        v___y_2032_,
    );
    leanh::lean_dec(v___y_2032_);
    leanh::lean_dec_ref(v___y_2031_);
    leanh::lean_dec(v___y_2030_);
    leanh::lean_dec_ref(v___y_2029_);
    return v_res_2035_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(
    mut v_00_u03b1_2036_: *mut leanh::LeanObject,
    mut v_msg_2037_: *mut leanh::LeanObject,
    mut v___y_2038_: *mut leanh::LeanObject,
    mut v___y_2039_: *mut leanh::LeanObject,
    mut v___y_2040_: *mut leanh::LeanObject,
    mut v___y_2041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(
        v_msg_2037_,
        v___y_2038_,
        v___y_2039_,
        v___y_2040_,
        v___y_2041_,
    );
    return v___x_2043_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(
    mut v_00_u03b1_2044_: *mut leanh::LeanObject,
    mut v_msg_2045_: *mut leanh::LeanObject,
    mut v___y_2046_: *mut leanh::LeanObject,
    mut v___y_2047_: *mut leanh::LeanObject,
    mut v___y_2048_: *mut leanh::LeanObject,
    mut v___y_2049_: *mut leanh::LeanObject,
    mut v___y_2050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(
        v_00_u03b1_2044_,
        v_msg_2045_,
        v___y_2046_,
        v___y_2047_,
        v___y_2048_,
        v___y_2049_,
    );
    leanh::lean_dec(v___y_2049_);
    leanh::lean_dec_ref(v___y_2048_);
    leanh::lean_dec(v___y_2047_);
    leanh::lean_dec_ref(v___y_2046_);
    return v_res_2051_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(
    mut v_env_2052_: *mut leanh::LeanObject,
    mut v___y_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_2052_, v___y_2054_, v___y_2056_);
    return v___x_2058_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(
    mut v_env_2059_: *mut leanh::LeanObject,
    mut v___y_2060_: *mut leanh::LeanObject,
    mut v___y_2061_: *mut leanh::LeanObject,
    mut v___y_2062_: *mut leanh::LeanObject,
    mut v___y_2063_: *mut leanh::LeanObject,
    mut v___y_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2065_ =
        l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(
            v_env_2059_,
            v___y_2060_,
            v___y_2061_,
            v___y_2062_,
            v___y_2063_,
        );
    leanh::lean_dec(v___y_2063_);
    leanh::lean_dec_ref(v___y_2062_);
    leanh::lean_dec(v___y_2061_);
    leanh::lean_dec_ref(v___y_2060_);
    return v_res_2065_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(
    mut v_00_u03b1_2066_: *mut leanh::LeanObject,
    mut v_env_2067_: *mut leanh::LeanObject,
    mut v_x_2068_: *mut leanh::LeanObject,
    mut v___y_2069_: *mut leanh::LeanObject,
    mut v___y_2070_: *mut leanh::LeanObject,
    mut v___y_2071_: *mut leanh::LeanObject,
    mut v___y_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2074_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(
        v_env_2067_,
        v_x_2068_,
        v___y_2069_,
        v___y_2070_,
        v___y_2071_,
        v___y_2072_,
    );
    return v___x_2074_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(
    mut v_00_u03b1_2075_: *mut leanh::LeanObject,
    mut v_env_2076_: *mut leanh::LeanObject,
    mut v_x_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2083_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(
        v_00_u03b1_2075_,
        v_env_2076_,
        v_x_2077_,
        v___y_2078_,
        v___y_2079_,
        v___y_2080_,
        v___y_2081_,
    );
    leanh::lean_dec(v___y_2081_);
    leanh::lean_dec_ref(v___y_2080_);
    leanh::lean_dec(v___y_2079_);
    leanh::lean_dec_ref(v___y_2078_);
    return v_res_2083_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(
    mut v_00_u03b1_2084_: *mut leanh::LeanObject,
    mut v_x_2085_: *mut leanh::LeanObject,
    mut v___y_2086_: *mut leanh::LeanObject,
    mut v___y_2087_: *mut leanh::LeanObject,
    mut v___y_2088_: *mut leanh::LeanObject,
    mut v___y_2089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2091_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
    return v___x_2091_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(
    mut v_00_u03b1_2092_: *mut leanh::LeanObject,
    mut v_x_2093_: *mut leanh::LeanObject,
    mut v___y_2094_: *mut leanh::LeanObject,
    mut v___y_2095_: *mut leanh::LeanObject,
    mut v___y_2096_: *mut leanh::LeanObject,
    mut v___y_2097_: *mut leanh::LeanObject,
    mut v___y_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2099_ =
        l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(
            v_00_u03b1_2092_,
            v_x_2093_,
            v___y_2094_,
            v___y_2095_,
            v___y_2096_,
            v___y_2097_,
        );
    leanh::lean_dec(v___y_2097_);
    leanh::lean_dec_ref(v___y_2096_);
    leanh::lean_dec(v___y_2095_);
    leanh::lean_dec_ref(v___y_2094_);
    return v_res_2099_;
}
pub unsafe fn _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0;
    v___x_2102_ = l_Lean_stringToMessageData(v___x_2101_);
    return v___x_2102_;
}
pub unsafe fn l_Lean_Meta_evalExpr_x27___redArg___lam__0(
    mut v_typeName_2103_: *mut leanh::LeanObject,
    mut v_type_2104_: *mut leanh::LeanObject,
    mut v___y_2105_: *mut leanh::LeanObject,
    mut v___y_2106_: *mut leanh::LeanObject,
    mut v___y_2107_: *mut leanh::LeanObject,
    mut v___y_2108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_a_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2110_ = l_Lean_Meta_whnfD(
                    v_type_2104_,
                    v___y_2105_,
                    v___y_2106_,
                    v___y_2107_,
                    v___y_2108_,
                );
                if leanh::lean_obj_tag(v___x_2110_) == 0 {
                    v_a_2111_ = leanh::lean_ctor_get(v___x_2110_, 0);
                    v_isSharedCheck_2124_ = (!leanh::lean_is_exclusive(v___x_2110_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v___x_2113_ = v___x_2110_;
                        v_isShared_2114_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2111_);
                        leanh::lean_dec(v___x_2110_);
                        v___x_2113_ = leanh::lean_box(0);
                        v_isShared_2114_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2125_ = leanh::lean_ctor_get(v___x_2110_, 0);
                    v_isSharedCheck_2132_ = (!leanh::lean_is_exclusive(v___x_2110_)) as u8;
                    if v_isSharedCheck_2132_ == 0 {
                        v___x_2127_ = v___x_2110_;
                        v_isShared_2128_ = v_isSharedCheck_2132_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2125_);
                        leanh::lean_dec(v___x_2110_);
                        v___x_2127_ = leanh::lean_box(0);
                        v_isShared_2128_ = v_isSharedCheck_2132_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2115_ = l_Lean_Expr_isConstOf(v_a_2111_, v_typeName_2103_);
                if v___x_2115_ == 0 {
                    leanh::lean_del_object(v___x_2113_);
                    v___x_2116_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1,
                    );
                    v___x_2117_ = l_Lean_indentExpr(v_a_2111_);
                    v___x_2118_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2118_, 0, v___x_2116_);
                    leanh::lean_ctor_set(v___x_2118_, 1, v___x_2117_);
                    v___x_2119_ =
                        l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(
                            v___x_2118_,
                            v___y_2105_,
                            v___y_2106_,
                            v___y_2107_,
                            v___y_2108_,
                        );
                    return v___x_2119_;
                } else {
                    leanh::lean_dec(v_a_2111_);
                    v___x_2120_ = leanh::lean_box(0);
                    if v_isShared_2114_ == 0 {
                        leanh::lean_ctor_set(v___x_2113_, 0, v___x_2120_);
                        v___x_2122_ = v___x_2113_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2123_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
                        v___x_2122_ = v_reuseFailAlloc_2123_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2122_;
            }
            3 => {
                if v_isShared_2128_ == 0 {
                    v___x_2130_ = v___x_2127_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2131_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
                    v___x_2130_ = v_reuseFailAlloc_2131_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(
    mut v_typeName_2133_: *mut leanh::LeanObject,
    mut v_type_2134_: *mut leanh::LeanObject,
    mut v___y_2135_: *mut leanh::LeanObject,
    mut v___y_2136_: *mut leanh::LeanObject,
    mut v___y_2137_: *mut leanh::LeanObject,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(
        v_typeName_2133_,
        v_type_2134_,
        v___y_2135_,
        v___y_2136_,
        v___y_2137_,
        v___y_2138_,
    );
    leanh::lean_dec(v___y_2138_);
    leanh::lean_dec_ref(v___y_2137_);
    leanh::lean_dec(v___y_2136_);
    leanh::lean_dec_ref(v___y_2135_);
    leanh::lean_dec(v_typeName_2133_);
    return v_res_2140_;
}
pub unsafe fn l_Lean_Meta_evalExpr_x27___redArg(
    mut v_typeName_2141_: *mut leanh::LeanObject,
    mut v_value_2142_: *mut leanh::LeanObject,
    mut v_safety_2143_: u8,
    mut v_checkMeta_2144_: u8,
    mut v_a_2145_: *mut leanh::LeanObject,
    mut v_a_2146_: *mut leanh::LeanObject,
    mut v_a_2147_: *mut leanh::LeanObject,
    mut v_a_2148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2150_ = leanh::lean_alloc_closure(
        l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_2150_, 0, v_typeName_2141_);
    v___x_2151_ = l_Lean_Meta_evalExprCore___redArg(
        v_value_2142_,
        v___f_2150_,
        v_safety_2143_,
        v_checkMeta_2144_,
        v_a_2145_,
        v_a_2146_,
        v_a_2147_,
        v_a_2148_,
    );
    return v___x_2151_;
}
pub unsafe fn l_Lean_Meta_evalExpr_x27___redArg___boxed(
    mut v_typeName_2152_: *mut leanh::LeanObject,
    mut v_value_2153_: *mut leanh::LeanObject,
    mut v_safety_2154_: *mut leanh::LeanObject,
    mut v_checkMeta_2155_: *mut leanh::LeanObject,
    mut v_a_2156_: *mut leanh::LeanObject,
    mut v_a_2157_: *mut leanh::LeanObject,
    mut v_a_2158_: *mut leanh::LeanObject,
    mut v_a_2159_: *mut leanh::LeanObject,
    mut v_a_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_safety_boxed_2161_: u8 = 0;
    let mut v_checkMeta_boxed_2162_: u8 = 0;
    let mut v_res_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_safety_boxed_2161_ = (leanh::lean_unbox(v_safety_2154_) as u8);
    v_checkMeta_boxed_2162_ = (leanh::lean_unbox(v_checkMeta_2155_) as u8);
    v_res_2163_ = l_Lean_Meta_evalExpr_x27___redArg(
        v_typeName_2152_,
        v_value_2153_,
        v_safety_boxed_2161_,
        v_checkMeta_boxed_2162_,
        v_a_2156_,
        v_a_2157_,
        v_a_2158_,
        v_a_2159_,
    );
    leanh::lean_dec(v_a_2159_);
    leanh::lean_dec_ref(v_a_2158_);
    leanh::lean_dec(v_a_2157_);
    leanh::lean_dec_ref(v_a_2156_);
    return v_res_2163_;
}
pub unsafe fn l_Lean_Meta_evalExpr_x27(
    mut v_00_u03b1_2164_: *mut leanh::LeanObject,
    mut v_typeName_2165_: *mut leanh::LeanObject,
    mut v_value_2166_: *mut leanh::LeanObject,
    mut v_safety_2167_: u8,
    mut v_checkMeta_2168_: u8,
    mut v_a_2169_: *mut leanh::LeanObject,
    mut v_a_2170_: *mut leanh::LeanObject,
    mut v_a_2171_: *mut leanh::LeanObject,
    mut v_a_2172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2174_ = l_Lean_Meta_evalExpr_x27___redArg(
        v_typeName_2165_,
        v_value_2166_,
        v_safety_2167_,
        v_checkMeta_2168_,
        v_a_2169_,
        v_a_2170_,
        v_a_2171_,
        v_a_2172_,
    );
    return v___x_2174_;
}
pub unsafe fn l_Lean_Meta_evalExpr_x27___boxed(
    mut v_00_u03b1_2175_: *mut leanh::LeanObject,
    mut v_typeName_2176_: *mut leanh::LeanObject,
    mut v_value_2177_: *mut leanh::LeanObject,
    mut v_safety_2178_: *mut leanh::LeanObject,
    mut v_checkMeta_2179_: *mut leanh::LeanObject,
    mut v_a_2180_: *mut leanh::LeanObject,
    mut v_a_2181_: *mut leanh::LeanObject,
    mut v_a_2182_: *mut leanh::LeanObject,
    mut v_a_2183_: *mut leanh::LeanObject,
    mut v_a_2184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_safety_boxed_2185_: u8 = 0;
    let mut v_checkMeta_boxed_2186_: u8 = 0;
    let mut v_res_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_safety_boxed_2185_ = (leanh::lean_unbox(v_safety_2178_) as u8);
    v_checkMeta_boxed_2186_ = (leanh::lean_unbox(v_checkMeta_2179_) as u8);
    v_res_2187_ = l_Lean_Meta_evalExpr_x27(
        v_00_u03b1_2175_,
        v_typeName_2176_,
        v_value_2177_,
        v_safety_boxed_2185_,
        v_checkMeta_boxed_2186_,
        v_a_2180_,
        v_a_2181_,
        v_a_2182_,
        v_a_2183_,
    );
    leanh::lean_dec(v_a_2183_);
    leanh::lean_dec_ref(v_a_2182_);
    leanh::lean_dec(v_a_2181_);
    leanh::lean_dec_ref(v_a_2180_);
    return v_res_2187_;
}
pub unsafe fn _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = l_Lean_Meta_evalExpr___redArg___lam__0___closed__1;
    v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
    return v___x_2192_;
}
pub unsafe fn l_Lean_Meta_evalExpr___redArg___lam__0(
    mut v_expectedType_2193_: *mut leanh::LeanObject,
    mut v_type_2194_: *mut leanh::LeanObject,
    mut v___y_2195_: *mut leanh::LeanObject,
    mut v___y_2196_: *mut leanh::LeanObject,
    mut v___y_2197_: *mut leanh::LeanObject,
    mut v___y_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2204_: u8 = 0;
    let mut v___x_2205_: u8 = 0;
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2220_: u8 = 0;
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v_a_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_expectedType_2193_);
                leanh::lean_inc_ref(v_type_2194_);
                v___x_2200_ = l_Lean_Meta_isExprDefEq(
                    v_type_2194_,
                    v_expectedType_2193_,
                    v___y_2195_,
                    v___y_2196_,
                    v___y_2197_,
                    v___y_2198_,
                );
                if leanh::lean_obj_tag(v___x_2200_) == 0 {
                    v_a_2201_ = leanh::lean_ctor_get(v___x_2200_, 0);
                    v_isSharedCheck_2225_ = (!leanh::lean_is_exclusive(v___x_2200_)) as u8;
                    if v_isSharedCheck_2225_ == 0 {
                        v___x_2203_ = v___x_2200_;
                        v_isShared_2204_ = v_isSharedCheck_2225_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2201_);
                        leanh::lean_dec(v___x_2200_);
                        v___x_2203_ = leanh::lean_box(0);
                        v_isShared_2204_ = v_isSharedCheck_2225_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_type_2194_);
                    leanh::lean_dec_ref(v_expectedType_2193_);
                    v_a_2226_ = leanh::lean_ctor_get(v___x_2200_, 0);
                    v_isSharedCheck_2233_ = (!leanh::lean_is_exclusive(v___x_2200_)) as u8;
                    if v_isSharedCheck_2233_ == 0 {
                        v___x_2228_ = v___x_2200_;
                        v_isShared_2229_ = v_isSharedCheck_2233_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2226_);
                        leanh::lean_dec(v___x_2200_);
                        v___x_2228_ = leanh::lean_box(0);
                        v_isShared_2229_ = v_isSharedCheck_2233_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2205_ = (leanh::lean_unbox(v_a_2201_) as u8);
                leanh::lean_dec(v_a_2201_);
                if v___x_2205_ == 0 {
                    leanh::lean_del_object(v___x_2203_);
                    v___x_2206_ = leanh::lean_box(0);
                    v___x_2207_ = l_Lean_Meta_evalExpr___redArg___lam__0___closed__0;
                    v___x_2208_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(
                        v_type_2194_,
                        v_expectedType_2193_,
                        v___x_2206_,
                        v___x_2207_,
                    );
                    if leanh::lean_obj_tag(v___x_2208_) == 0 {
                        v_a_2209_ = leanh::lean_ctor_get(v___x_2208_, 0);
                        leanh::lean_inc(v_a_2209_);
                        leanh::lean_dec_ref_known(v___x_2208_, 1);
                        v___x_2210_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_evalExpr___redArg___lam__0___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once
                            ),
                            _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2,
                        );
                        v___x_2211_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2211_, 0, v___x_2210_);
                        leanh::lean_ctor_set(v___x_2211_, 1, v_a_2209_);
                        v___x_2212_ =
                            l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(
                                v___x_2211_,
                                v___y_2195_,
                                v___y_2196_,
                                v___y_2197_,
                                v___y_2198_,
                            );
                        return v___x_2212_;
                    } else {
                        v_a_2213_ = leanh::lean_ctor_get(v___x_2208_, 0);
                        v_isSharedCheck_2220_ =
                            (!leanh::lean_is_exclusive(v___x_2208_)) as u8;
                        if v_isSharedCheck_2220_ == 0 {
                            v___x_2215_ = v___x_2208_;
                            v_isShared_2216_ = v_isSharedCheck_2220_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2213_);
                            leanh::lean_dec(v___x_2208_);
                            v___x_2215_ = leanh::lean_box(0);
                            v_isShared_2216_ = v_isSharedCheck_2220_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_type_2194_);
                    leanh::lean_dec_ref(v_expectedType_2193_);
                    v___x_2221_ = leanh::lean_box(0);
                    if v_isShared_2204_ == 0 {
                        leanh::lean_ctor_set(v___x_2203_, 0, v___x_2221_);
                        v___x_2223_ = v___x_2203_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2224_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
                        v___x_2223_ = v_reuseFailAlloc_2224_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2216_ == 0 {
                    v___x_2218_ = v___x_2215_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
                    v___x_2218_ = v_reuseFailAlloc_2219_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2218_;
            }
            4 => {
                return v___x_2223_;
            }
            5 => {
                if v_isShared_2229_ == 0 {
                    v___x_2231_ = v___x_2228_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
                    v___x_2231_ = v_reuseFailAlloc_2232_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_evalExpr___redArg___lam__0___boxed(
    mut v_expectedType_2234_: *mut leanh::LeanObject,
    mut v_type_2235_: *mut leanh::LeanObject,
    mut v___y_2236_: *mut leanh::LeanObject,
    mut v___y_2237_: *mut leanh::LeanObject,
    mut v___y_2238_: *mut leanh::LeanObject,
    mut v___y_2239_: *mut leanh::LeanObject,
    mut v___y_2240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2241_ = l_Lean_Meta_evalExpr___redArg___lam__0(
        v_expectedType_2234_,
        v_type_2235_,
        v___y_2236_,
        v___y_2237_,
        v___y_2238_,
        v___y_2239_,
    );
    leanh::lean_dec(v___y_2239_);
    leanh::lean_dec_ref(v___y_2238_);
    leanh::lean_dec(v___y_2237_);
    leanh::lean_dec_ref(v___y_2236_);
    return v_res_2241_;
}
pub unsafe fn l_Lean_Meta_evalExpr___redArg(
    mut v_expectedType_2242_: *mut leanh::LeanObject,
    mut v_value_2243_: *mut leanh::LeanObject,
    mut v_safety_2244_: u8,
    mut v_checkMeta_2245_: u8,
    mut v_a_2246_: *mut leanh::LeanObject,
    mut v_a_2247_: *mut leanh::LeanObject,
    mut v_a_2248_: *mut leanh::LeanObject,
    mut v_a_2249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2251_ = leanh::lean_alloc_closure(
        l_Lean_Meta_evalExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_2251_, 0, v_expectedType_2242_);
    v___x_2252_ = l_Lean_Meta_evalExprCore___redArg(
        v_value_2243_,
        v___f_2251_,
        v_safety_2244_,
        v_checkMeta_2245_,
        v_a_2246_,
        v_a_2247_,
        v_a_2248_,
        v_a_2249_,
    );
    return v___x_2252_;
}
pub unsafe fn l_Lean_Meta_evalExpr___redArg___boxed(
    mut v_expectedType_2253_: *mut leanh::LeanObject,
    mut v_value_2254_: *mut leanh::LeanObject,
    mut v_safety_2255_: *mut leanh::LeanObject,
    mut v_checkMeta_2256_: *mut leanh::LeanObject,
    mut v_a_2257_: *mut leanh::LeanObject,
    mut v_a_2258_: *mut leanh::LeanObject,
    mut v_a_2259_: *mut leanh::LeanObject,
    mut v_a_2260_: *mut leanh::LeanObject,
    mut v_a_2261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_safety_boxed_2262_: u8 = 0;
    let mut v_checkMeta_boxed_2263_: u8 = 0;
    let mut v_res_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_safety_boxed_2262_ = (leanh::lean_unbox(v_safety_2255_) as u8);
    v_checkMeta_boxed_2263_ = (leanh::lean_unbox(v_checkMeta_2256_) as u8);
    v_res_2264_ = l_Lean_Meta_evalExpr___redArg(
        v_expectedType_2253_,
        v_value_2254_,
        v_safety_boxed_2262_,
        v_checkMeta_boxed_2263_,
        v_a_2257_,
        v_a_2258_,
        v_a_2259_,
        v_a_2260_,
    );
    leanh::lean_dec(v_a_2260_);
    leanh::lean_dec_ref(v_a_2259_);
    leanh::lean_dec(v_a_2258_);
    leanh::lean_dec_ref(v_a_2257_);
    return v_res_2264_;
}
pub unsafe fn l_Lean_Meta_evalExpr(
    mut v_00_u03b1_2265_: *mut leanh::LeanObject,
    mut v_expectedType_2266_: *mut leanh::LeanObject,
    mut v_value_2267_: *mut leanh::LeanObject,
    mut v_safety_2268_: u8,
    mut v_checkMeta_2269_: u8,
    mut v_a_2270_: *mut leanh::LeanObject,
    mut v_a_2271_: *mut leanh::LeanObject,
    mut v_a_2272_: *mut leanh::LeanObject,
    mut v_a_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2275_ = l_Lean_Meta_evalExpr___redArg(
        v_expectedType_2266_,
        v_value_2267_,
        v_safety_2268_,
        v_checkMeta_2269_,
        v_a_2270_,
        v_a_2271_,
        v_a_2272_,
        v_a_2273_,
    );
    return v___x_2275_;
}
pub unsafe fn l_Lean_Meta_evalExpr___boxed(
    mut v_00_u03b1_2276_: *mut leanh::LeanObject,
    mut v_expectedType_2277_: *mut leanh::LeanObject,
    mut v_value_2278_: *mut leanh::LeanObject,
    mut v_safety_2279_: *mut leanh::LeanObject,
    mut v_checkMeta_2280_: *mut leanh::LeanObject,
    mut v_a_2281_: *mut leanh::LeanObject,
    mut v_a_2282_: *mut leanh::LeanObject,
    mut v_a_2283_: *mut leanh::LeanObject,
    mut v_a_2284_: *mut leanh::LeanObject,
    mut v_a_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_safety_boxed_2286_: u8 = 0;
    let mut v_checkMeta_boxed_2287_: u8 = 0;
    let mut v_res_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_safety_boxed_2286_ = (leanh::lean_unbox(v_safety_2279_) as u8);
    v_checkMeta_boxed_2287_ = (leanh::lean_unbox(v_checkMeta_2280_) as u8);
    v_res_2288_ = l_Lean_Meta_evalExpr(
        v_00_u03b1_2276_,
        v_expectedType_2277_,
        v_value_2278_,
        v_safety_boxed_2286_,
        v_checkMeta_boxed_2287_,
        v_a_2281_,
        v_a_2282_,
        v_a_2283_,
        v_a_2284_,
    );
    leanh::lean_dec(v_a_2284_);
    leanh::lean_dec_ref(v_a_2283_);
    leanh::lean_dec(v_a_2282_);
    leanh::lean_dec_ref(v_a_2281_);
    return v_res_2288_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Eval(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Eval(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Eval(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLevelParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Eval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Eval(builtin);
}
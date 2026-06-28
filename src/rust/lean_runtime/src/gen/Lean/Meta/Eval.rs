// Lean compiler output
// Module: Lean.Meta.Eval
// Imports: Lean.AddDecl Lean.Meta.Check Lean.Util.CollectLevelParams Lean.Compiler.Options
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget_borrowed, lean_mk_array};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_dec_lt,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::MonadEnv::lean_has_compile_error;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value)
                as *mut LeanObject,
            17409515008221977244 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_value: LeanStringObject<57> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 57,
        m_capacity: 57,
        m_length: 56,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 118, 97, 108, 117, 97, 116, 101,
            32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 44, 32, 105, 116, 32, 99, 111,
            110, 116, 97, 105, 110, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108,
            101, 115, 0,
        ],
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 97, 116,
            32, 101, 118, 97, 108, 69, 120, 112, 114, 0,
        ],
    };
static mut l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_evalExpr___redArg___lam__0___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_evalExpr___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_evalExpr___redArg___lam__0___closed__1_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 97, 116,
            32, 96, 101, 118, 97, 108, 69, 120, 112, 114, 96, 32, 0,
        ],
    };
static mut l_Lean_Meta_evalExpr___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_evalExpr___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(
    mut v_e_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1162_: u8 = 0;
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1168_: u8 = 0;
    let mut v_unused_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1148_ = l_Lean_Expr_hasMVar(v_e_1145_);
                if v___x_1148_ == 0 {
                    v___x_1149_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1149_, 0, v_e_1145_);
                    return v___x_1149_;
                } else {
                    v___x_1150_ = lean_st_ref_get(v___y_1146_);
                    v_mctx_1151_ = lean_ctor_get(v___x_1150_, 0);
                    lean_inc_ref(v_mctx_1151_);
                    lean_dec(v___x_1150_);
                    v___x_1152_ = l_Lean_instantiateMVarsCore(v_mctx_1151_, v_e_1145_);
                    v_fst_1153_ = lean_ctor_get(v___x_1152_, 0);
                    lean_inc(v_fst_1153_);
                    v_snd_1154_ = lean_ctor_get(v___x_1152_, 1);
                    lean_inc(v_snd_1154_);
                    lean_dec_ref(v___x_1152_);
                    v___x_1155_ = lean_st_ref_take(v___y_1146_);
                    v_cache_1156_ = lean_ctor_get(v___x_1155_, 1);
                    v_zetaDeltaFVarIds_1157_ = lean_ctor_get(v___x_1155_, 2);
                    v_postponed_1158_ = lean_ctor_get(v___x_1155_, 3);
                    v_diag_1159_ = lean_ctor_get(v___x_1155_, 4);
                    v_isSharedCheck_1168_ = (!lean_is_exclusive(v___x_1155_)) as u8;
                    if v_isSharedCheck_1168_ == 0 {
                        v_unused_1169_ = lean_ctor_get(v___x_1155_, 0);
                        lean_dec(v_unused_1169_);
                        v___x_1161_ = v___x_1155_;
                        v_isShared_1162_ = v_isSharedCheck_1168_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1159_);
                        lean_inc(v_postponed_1158_);
                        lean_inc(v_zetaDeltaFVarIds_1157_);
                        lean_inc(v_cache_1156_);
                        lean_dec(v___x_1155_);
                        v___x_1161_ = lean_box(0);
                        v_isShared_1162_ = v_isSharedCheck_1168_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1162_ == 0 {
                    lean_ctor_set(v___x_1161_, 0, v_snd_1154_);
                    v___x_1164_ = v___x_1161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_snd_1154_);
                    lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_cache_1156_);
                    lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_zetaDeltaFVarIds_1157_);
                    lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_postponed_1158_);
                    lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_diag_1159_);
                    v___x_1164_ = v_reuseFailAlloc_1167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1165_ = lean_st_ref_set(v___y_1146_, v___x_1164_);
                v___x_1166_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1166_, 0, v_fst_1153_);
                return v___x_1166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg___boxed(
    mut v_e_1170_: *mut LeanObject,
    mut v___y_1171_: *mut LeanObject,
    mut v___y_1172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1173_: *mut LeanObject = core::ptr::null_mut();
    v_res_1173_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(
        v_e_1170_,
        v___y_1171_,
    );
    lean_dec(v___y_1171_);
    return v_res_1173_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(
    mut v_e_1174_: *mut LeanObject,
    mut v___y_1175_: *mut LeanObject,
    mut v___y_1176_: *mut LeanObject,
    mut v___y_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    v___x_1180_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(
        v_e_1174_,
        v___y_1176_,
    );
    return v___x_1180_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___boxed(
    mut v_e_1181_: *mut LeanObject,
    mut v___y_1182_: *mut LeanObject,
    mut v___y_1183_: *mut LeanObject,
    mut v___y_1184_: *mut LeanObject,
    mut v___y_1185_: *mut LeanObject,
    mut v___y_1186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1187_: *mut LeanObject = core::ptr::null_mut();
    v_res_1187_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(
        v_e_1181_,
        v___y_1182_,
        v___y_1183_,
        v___y_1184_,
        v___y_1185_,
    );
    lean_dec(v___y_1185_);
    lean_dec_ref(v___y_1184_);
    lean_dec(v___y_1183_);
    lean_dec_ref(v___y_1182_);
    return v_res_1187_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(
    mut v_opts_1188_: *mut LeanObject,
    mut v_opt_1189_: *mut LeanObject,
) -> u8 {
    let mut v_name_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    v_name_1190_ = lean_ctor_get(v_opt_1189_, 0);
    v_defValue_1191_ = lean_ctor_get(v_opt_1189_, 1);
    v_map_1192_ = lean_ctor_get(v_opts_1188_, 0);
    v___x_1193_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1192_,
            v_name_1190_,
        );
    if lean_obj_tag(v___x_1193_) == 0 {
        let mut v___x_1194_: u8 = 0;
        v___x_1194_ = (lean_unbox(v_defValue_1191_) as u8);
        return v___x_1194_;
    } else {
        let mut v_val_1195_: *mut LeanObject = core::ptr::null_mut();
        v_val_1195_ = lean_ctor_get(v___x_1193_, 0);
        lean_inc(v_val_1195_);
        lean_dec_ref_known(v___x_1193_, 1);
        if lean_obj_tag(v_val_1195_) == 1 {
            let mut v_v_1196_: u8 = 0;
            v_v_1196_ = lean_ctor_get_uint8(v_val_1195_, 0 as u32);
            lean_dec_ref_known(v_val_1195_, 0);
            return v_v_1196_;
        } else {
            let mut v___x_1197_: u8 = 0;
            lean_dec(v_val_1195_);
            v___x_1197_ = (lean_unbox(v_defValue_1191_) as u8);
            return v___x_1197_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(
    mut v_opts_1198_: *mut LeanObject,
    mut v_opt_1199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1200_: u8 = 0;
    let mut v_r_1201_: *mut LeanObject = core::ptr::null_mut();
    v_res_1200_ =
        l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v_opts_1198_, v_opt_1199_);
    lean_dec_ref(v_opt_1199_);
    lean_dec_ref(v_opts_1198_);
    v_r_1201_ = lean_box((v_res_1200_) as usize);
    return v_r_1201_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(
    mut v_opts_1202_: *mut LeanObject,
    mut v_opt_1203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    v_name_1204_ = lean_ctor_get(v_opt_1203_, 0);
    v_defValue_1205_ = lean_ctor_get(v_opt_1203_, 1);
    v_map_1206_ = lean_ctor_get(v_opts_1202_, 0);
    v___x_1207_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1206_,
            v_name_1204_,
        );
    if lean_obj_tag(v___x_1207_) == 0 {
        lean_inc(v_defValue_1205_);
        return v_defValue_1205_;
    } else {
        let mut v_val_1208_: *mut LeanObject = core::ptr::null_mut();
        v_val_1208_ = lean_ctor_get(v___x_1207_, 0);
        lean_inc(v_val_1208_);
        lean_dec_ref_known(v___x_1207_, 1);
        if lean_obj_tag(v_val_1208_) == 3 {
            let mut v_v_1209_: *mut LeanObject = core::ptr::null_mut();
            v_v_1209_ = lean_ctor_get(v_val_1208_, 0);
            lean_inc(v_v_1209_);
            lean_dec_ref_known(v_val_1208_, 1);
            return v_v_1209_;
        } else {
            lean_dec(v_val_1208_);
            lean_inc(v_defValue_1205_);
            return v_defValue_1205_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3___boxed(
    mut v_opts_1210_: *mut LeanObject,
    mut v_opt_1211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1212_: *mut LeanObject = core::ptr::null_mut();
    v_res_1212_ =
        l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v_opts_1210_, v_opt_1211_);
    lean_dec_ref(v_opt_1211_);
    lean_dec_ref(v_opts_1210_);
    return v_res_1212_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(
    mut v_msgData_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    v___x_1219_ = lean_st_ref_get(v___y_1217_);
    v_env_1220_ = lean_ctor_get(v___x_1219_, 0);
    lean_inc_ref(v_env_1220_);
    lean_dec(v___x_1219_);
    v___x_1221_ = lean_st_ref_get(v___y_1215_);
    v_mctx_1222_ = lean_ctor_get(v___x_1221_, 0);
    lean_inc_ref(v_mctx_1222_);
    lean_dec(v___x_1221_);
    v_lctx_1223_ = lean_ctor_get(v___y_1214_, 2);
    v_options_1224_ = lean_ctor_get(v___y_1216_, 2);
    lean_inc_ref(v_options_1224_);
    lean_inc_ref(v_lctx_1223_);
    v___x_1225_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1225_, 0, v_env_1220_);
    lean_ctor_set(v___x_1225_, 1, v_mctx_1222_);
    lean_ctor_set(v___x_1225_, 2, v_lctx_1223_);
    lean_ctor_set(v___x_1225_, 3, v_options_1224_);
    v___x_1226_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1226_, 0, v___x_1225_);
    lean_ctor_set(v___x_1226_, 1, v_msgData_1213_);
    v___x_1227_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1227_, 0, v___x_1226_);
    return v___x_1227_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8___boxed(
    mut v_msgData_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
    mut v___y_1231_: *mut LeanObject,
    mut v___y_1232_: *mut LeanObject,
    mut v___y_1233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1234_: *mut LeanObject = core::ptr::null_mut();
    v_res_1234_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(v_msgData_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
    lean_dec(v___y_1232_);
    lean_dec_ref(v___y_1231_);
    lean_dec(v___y_1230_);
    lean_dec_ref(v___y_1229_);
    return v_res_1234_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(
    mut v_msg_1235_: *mut LeanObject,
    mut v___y_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
    mut v___y_1239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1241_ = lean_ctor_get(v___y_1238_, 5);
                v___x_1242_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(v_msg_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
                v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
                v_isSharedCheck_1251_ = (!lean_is_exclusive(v___x_1242_)) as u8;
                if v_isSharedCheck_1251_ == 0 {
                    v___x_1245_ = v___x_1242_;
                    v_isShared_1246_ = v_isSharedCheck_1251_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1243_);
                    lean_dec(v___x_1242_);
                    v___x_1245_ = lean_box(0);
                    v_isShared_1246_ = v_isSharedCheck_1251_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1241_);
                v___x_1247_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1247_, 0, v_ref_1241_);
                lean_ctor_set(v___x_1247_, 1, v_a_1243_);
                if v_isShared_1246_ == 0 {
                    lean_ctor_set_tag(v___x_1245_, 1);
                    lean_ctor_set(v___x_1245_, 0, v___x_1247_);
                    v___x_1249_ = v___x_1245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
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
    mut v_msg_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1258_: *mut LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(
        v_msg_1252_,
        v___y_1253_,
        v___y_1254_,
        v___y_1255_,
        v___y_1256_,
    );
    lean_dec(v___y_1256_);
    lean_dec_ref(v___y_1255_);
    lean_dec(v___y_1254_);
    lean_dec_ref(v___y_1253_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(
    mut v_x_1259_: *mut LeanObject,
    mut v___y_1260_: *mut LeanObject,
    mut v___y_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1259_) == 0 {
                    v_a_1265_ = lean_ctor_get(v_x_1259_, 0);
                    lean_inc(v_a_1265_);
                    lean_dec_ref_known(v_x_1259_, 1);
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
                    v_a_1268_ = lean_ctor_get(v_x_1259_, 0);
                    v_isSharedCheck_1275_ = (!lean_is_exclusive(v_x_1259_)) as u8;
                    if v_isSharedCheck_1275_ == 0 {
                        v___x_1270_ = v_x_1259_;
                        v_isShared_1271_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1268_);
                        lean_dec(v_x_1259_);
                        v___x_1270_ = lean_box(0);
                        v_isShared_1271_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1271_ == 0 {
                    lean_ctor_set_tag(v___x_1270_, 0);
                    v___x_1273_ = v___x_1270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
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
    mut v_x_1276_: *mut LeanObject,
    mut v___y_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1282_: *mut LeanObject = core::ptr::null_mut();
    v_res_1282_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
    lean_dec(v___y_1280_);
    lean_dec_ref(v___y_1279_);
    lean_dec(v___y_1278_);
    lean_dec_ref(v___y_1277_);
    return v_res_1282_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    v___x_1283_ = lean_box(0);
    v___x_1284_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_1285_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1285_, 0, v___x_1284_);
    lean_ctor_set(v___x_1285_, 1, v___x_1283_);
    return v___x_1285_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg()
-> *mut LeanObject {
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    v___x_1287_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0);
    v___x_1288_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1288_, 0, v___x_1287_);
    return v___x_1288_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___boxed(
    mut v___y_1289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1290_: *mut LeanObject = core::ptr::null_mut();
    v_res_1290_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
    return v_res_1290_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(
    mut v_constName_1291_: *mut LeanObject,
    mut v_checkMeta_1292_: u8,
    mut v___y_1293_: *mut LeanObject,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: u8 = 0;
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1298_ = lean_st_ref_get(v___y_1296_);
                v_env_1299_ = lean_ctor_get(v___x_1298_, 0);
                lean_inc_ref(v_env_1299_);
                lean_dec(v___x_1298_);
                lean_inc(v_constName_1291_);
                v___x_1300_ = lean_has_compile_error(v_env_1299_, v_constName_1291_);
                if v___x_1300_ == 0 {
                    v___x_1301_ = lean_st_ref_get(v___y_1296_);
                    v_env_1302_ = lean_ctor_get(v___x_1301_, 0);
                    lean_inc_ref(v_env_1302_);
                    lean_dec(v___x_1301_);
                    v_options_1303_ = lean_ctor_get(v___y_1295_, 2);
                    v___x_1304_ = l_Lean_Environment_evalConst___redArg(
                        v_env_1302_,
                        v_options_1303_,
                        v_constName_1291_,
                        v_checkMeta_1292_,
                    );
                    lean_dec(v_constName_1291_);
                    lean_dec_ref(v_env_1302_);
                    v___x_1305_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v___x_1304_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
                    return v___x_1305_;
                } else {
                    v___x_1306_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
                    if lean_obj_tag(v___x_1306_) == 0 {
                        lean_dec_ref_known(v___x_1306_, 1);
                        v___x_1307_ = lean_st_ref_get(v___y_1296_);
                        v_env_1308_ = lean_ctor_get(v___x_1307_, 0);
                        lean_inc_ref(v_env_1308_);
                        lean_dec(v___x_1307_);
                        v_options_1309_ = lean_ctor_get(v___y_1295_, 2);
                        v___x_1310_ = l_Lean_Environment_evalConst___redArg(
                            v_env_1308_,
                            v_options_1309_,
                            v_constName_1291_,
                            v_checkMeta_1292_,
                        );
                        lean_dec(v_constName_1291_);
                        lean_dec_ref(v_env_1308_);
                        v___x_1311_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v___x_1310_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
                        return v___x_1311_;
                    } else {
                        lean_dec(v_constName_1291_);
                        v_a_1312_ = lean_ctor_get(v___x_1306_, 0);
                        v_isSharedCheck_1319_ = (!lean_is_exclusive(v___x_1306_)) as u8;
                        if v_isSharedCheck_1319_ == 0 {
                            v___x_1314_ = v___x_1306_;
                            v_isShared_1315_ = v_isSharedCheck_1319_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1312_);
                            lean_dec(v___x_1306_);
                            v___x_1314_ = lean_box(0);
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
                    v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
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
    mut v_constName_1320_: *mut LeanObject,
    mut v_checkMeta_1321_: *mut LeanObject,
    mut v___y_1322_: *mut LeanObject,
    mut v___y_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
    mut v___y_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checkMeta_boxed_1327_: u8 = 0;
    let mut v_res_1328_: *mut LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1327_ = (lean_unbox(v_checkMeta_1321_) as u8);
    v_res_1328_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(
        v_constName_1320_,
        v_checkMeta_boxed_1327_,
        v___y_1322_,
        v___y_1323_,
        v___y_1324_,
        v___y_1325_,
    );
    lean_dec(v___y_1325_);
    lean_dec_ref(v___y_1324_);
    lean_dec(v___y_1323_);
    lean_dec_ref(v___y_1322_);
    return v_res_1328_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(
    mut v___x_1329_: *mut LeanObject,
    mut v_as_1330_: *mut LeanObject,
    mut v_i_1331_: usize,
    mut v_stop_1332_: usize,
) -> u8 {
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: u8 = 0;
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_1341_: *mut LeanObject,
    mut v_as_1342_: *mut LeanObject,
    mut v_i_1343_: *mut LeanObject,
    mut v_stop_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1345_: usize = 0;
    let mut v_stop_boxed_1346_: usize = 0;
    let mut v_res_1347_: u8 = 0;
    let mut v_r_1348_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1345_ = lean_unbox_usize(v_i_1343_);
    lean_dec(v_i_1343_);
    v_stop_boxed_1346_ = lean_unbox_usize(v_stop_1344_);
    lean_dec(v_stop_1344_);
    v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v___x_1341_, v_as_1342_, v_i_boxed_1345_, v_stop_boxed_1346_);
    lean_dec_ref(v_as_1342_);
    lean_dec_ref(v___x_1341_);
    v_r_1348_ = lean_box((v_res_1347_) as usize);
    return v_r_1348_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(
    mut v_o_1352_: *mut LeanObject,
    mut v_k_1353_: *mut LeanObject,
    mut v_v_1354_: u8,
) -> *mut LeanObject {
    let mut v_map_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1356_: u8 = 0;
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1355_ = lean_ctor_get(v_o_1352_, 0);
                v_hasTrace_1356_ = lean_ctor_get_uint8(
                    v_o_1352_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1370_ = (!lean_is_exclusive(v_o_1352_)) as u8;
                if v_isSharedCheck_1370_ == 0 {
                    v___x_1358_ = v_o_1352_;
                    v_isShared_1359_ = v_isSharedCheck_1370_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_1355_);
                    lean_dec(v_o_1352_);
                    v___x_1358_ = lean_box(0);
                    v_isShared_1359_ = v_isSharedCheck_1370_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1360_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_1360_, 0 as u32, v_v_1354_);
                lean_inc(v_k_1353_);
                v___x_1361_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1353_, v___x_1360_, v_map_1355_);
                if v_hasTrace_1356_ == 0 {
                    v___x_1362_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1;
                    v___x_1363_ = l_Lean_Name_isPrefixOf(v___x_1362_, v_k_1353_);
                    lean_dec(v_k_1353_);
                    if v_isShared_1359_ == 0 {
                        lean_ctor_set(v___x_1358_, 0, v___x_1361_);
                        v___x_1365_ = v___x_1358_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1361_);
                        v___x_1365_ = v_reuseFailAlloc_1366_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_1353_);
                    if v_isShared_1359_ == 0 {
                        lean_ctor_set(v___x_1358_, 0, v___x_1361_);
                        v___x_1368_ = v___x_1358_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1361_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1369_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_1356_,
                        );
                        v___x_1368_ = v_reuseFailAlloc_1369_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_1365_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_o_1371_: *mut LeanObject,
    mut v_k_1372_: *mut LeanObject,
    mut v_v_1373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1374_: u8 = 0;
    let mut v_res_1375_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1374_ = (lean_unbox(v_v_1373_) as u8);
    v_res_1375_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(
            v_o_1371_,
            v_k_1372_,
            v_v_boxed_1374_,
        );
    return v_res_1375_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(
    mut v_opts_1376_: *mut LeanObject,
    mut v_opt_1377_: *mut LeanObject,
    mut v_val_1378_: u8,
) -> *mut LeanObject {
    let mut v_name_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    v_name_1379_ = lean_ctor_get(v_opt_1377_, 0);
    lean_inc(v_name_1379_);
    lean_dec_ref(v_opt_1377_);
    v___x_1380_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(
            v_opts_1376_,
            v_name_1379_,
            v_val_1378_,
        );
    return v___x_1380_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1___boxed(
    mut v_opts_1381_: *mut LeanObject,
    mut v_opt_1382_: *mut LeanObject,
    mut v_val_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_1384_: u8 = 0;
    let mut v_res_1385_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_1384_ = (lean_unbox(v_val_1383_) as u8);
    v_res_1385_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(
        v_opts_1381_,
        v_opt_1382_,
        v_val_boxed_1384_,
    );
    return v_res_1385_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    v___x_1386_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1386_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    v___x_1387_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once),
        _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0,
    );
    v___x_1388_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1388_, 0, v___x_1387_);
    return v___x_1388_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    v___x_1389_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once),
        _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1,
    );
    v___x_1390_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1390_, 0, v___x_1389_);
    lean_ctor_set(v___x_1390_, 1, v___x_1389_);
    return v___x_1390_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    v___x_1391_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once),
        _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1,
    );
    v___x_1392_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_1392_, 0, v___x_1391_);
    lean_ctor_set(v___x_1392_, 1, v___x_1391_);
    lean_ctor_set(v___x_1392_, 2, v___x_1391_);
    lean_ctor_set(v___x_1392_, 3, v___x_1391_);
    lean_ctor_set(v___x_1392_, 4, v___x_1391_);
    lean_ctor_set(v___x_1392_, 5, v___x_1391_);
    return v___x_1392_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7() -> *mut LeanObject {
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    v___x_1397_ = lean_box(0);
    v___x_1398_ = lean_unsigned_to_nat(16);
    v___x_1399_ = lean_mk_array(v___x_1398_, v___x_1397_);
    return v___x_1399_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8() -> *mut LeanObject {
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    v___x_1400_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once),
        _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7,
    );
    v___x_1401_ = lean_unsigned_to_nat(0);
    v___x_1402_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1402_, 0, v___x_1401_);
    lean_ctor_set(v___x_1402_, 1, v___x_1400_);
    return v___x_1402_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10() -> *mut LeanObject {
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    v___x_1405_ = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9;
    v___x_1406_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once),
        _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8,
    );
    v___x_1407_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1407_, 0, v___x_1406_);
    lean_ctor_set(v___x_1407_, 1, v___x_1406_);
    lean_ctor_set(v___x_1407_, 2, v___x_1405_);
    return v___x_1407_;
}
pub unsafe fn _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12() -> *mut LeanObject {
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    v___x_1409_ = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11;
    v___x_1410_ = l_Lean_stringToMessageData(v___x_1409_);
    return v___x_1410_;
}
pub unsafe fn l_Lean_Meta_evalExprCore___redArg___lam__0(
    mut v_checkMeta_1411_: u8,
    mut v_checkType_1412_: *mut LeanObject,
    mut v_safety_1413_: u8,
    mut v_value_1414_: *mut LeanObject,
    mut v___y_1415_: *mut LeanObject,
    mut v___y_1416_: *mut LeanObject,
    mut v___y_1417_: *mut LeanObject,
    mut v___y_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1421_: u8 = 0;
    let mut v___y_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1425_: u8 = 0;
    let mut v___y_1426_: u8 = 0;
    let mut v___y_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1441_: u8 = 0;
    let mut v_inheritedTraceOptions_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut v___y_1457_: u8 = 0;
    let mut v___y_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: u8 = 0;
    let mut v___y_1462_: u8 = 0;
    let mut v___y_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1479_: u8 = 0;
    let mut v_inheritedTraceOptions_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1482_: u8 = 0;
    let mut v___y_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1492_: u8 = 0;
    let mut v___y_1493_: u8 = 0;
    let mut v___y_1494_: u8 = 0;
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1506_: u8 = 0;
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_unused_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: u8 = 0;
    let mut v___y_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1517_: u8 = 0;
    let mut v___y_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: u8 = 0;
    let mut v___y_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1540_: u8 = 0;
    let mut v_inheritedTraceOptions_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1544_: u8 = 0;
    let mut v_env_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: u8 = 0;
    let mut v___x_1552_: u8 = 0;
    let mut v_reuseFailAlloc_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut v_unused_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: u8 = 0;
    let mut v___y_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: u8 = 0;
    let mut v___y_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1570_: u8 = 0;
    let mut v___y_1571_: u8 = 0;
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1589_: u8 = 0;
    let mut v_unused_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1592_: u8 = 0;
    let mut v___y_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1596_: u8 = 0;
    let mut v___y_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1598_: u8 = 0;
    let mut v___y_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1616_: u8 = 0;
    let mut v_inheritedTraceOptions_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v_env_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: u8 = 0;
    let mut v_reuseFailAlloc_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1631_: u8 = 0;
    let mut v_unused_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1635_: u8 = 0;
    let mut v___y_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1643_: u8 = 0;
    let mut v___y_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1645_: u8 = 0;
    let mut v___y_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1647_: u8 = 0;
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1659_: u8 = 0;
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut v_unused_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1690_: u8 = 0;
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: u8 = 0;
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: u8 = 0;
    let mut v_a_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1732_: u8 = 0;
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1736_: u8 = 0;
    let mut v_reuseFailAlloc_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_unused_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_unused_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1746_: u8 = 0;
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut v_a_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1758_: u8 = 0;
    let mut v___y_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: u8 = 0;
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1788_: u8 = 0;
    let mut v_a_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v_a_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut v_nextMacroScope_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v_unused_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v_env_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: usize = 0;
    let mut v___x_1852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1832_ = lean_st_ref_get(v___y_1418_);
                lean_inc_ref(v_value_1414_);
                v___x_1845_ = l_Lean_Expr_getUsedConstants(v_value_1414_);
                v___x_1846_ = lean_unsigned_to_nat(0);
                v___x_1847_ = lean_array_get_size(v___x_1845_);
                v___x_1848_ = lean_nat_dec_lt(v___x_1846_, v___x_1847_);
                if v___x_1848_ == 0 {
                    lean_dec_ref(v___x_1845_);
                    lean_dec(v___x_1832_);
                    state = 41;
                    continue;
                } else {
                    if v___x_1848_ == 0 {
                        lean_dec_ref(v___x_1845_);
                        lean_dec(v___x_1832_);
                        state = 41;
                        continue;
                    } else {
                        v_env_1849_ = lean_ctor_get(v___x_1832_, 0);
                        lean_inc_ref(v_env_1849_);
                        lean_dec(v___x_1832_);
                        v___x_1850_ = 0usize;
                        v___x_1851_ = lean_usize_of_nat(v___x_1847_);
                        v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_1849_, v___x_1845_, v___x_1850_, v___x_1851_);
                        lean_dec_ref(v___x_1845_);
                        lean_dec_ref(v_env_1849_);
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
                v___x_1445_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_1445_, 0, v_fileName_1430_);
                lean_ctor_set(v___x_1445_, 1, v_fileMap_1431_);
                lean_ctor_set(v___x_1445_, 2, v___y_1424_);
                lean_ctor_set(v___x_1445_, 3, v_currRecDepth_1432_);
                lean_ctor_set(v___x_1445_, 4, v___x_1444_);
                lean_ctor_set(v___x_1445_, 5, v_ref_1433_);
                lean_ctor_set(v___x_1445_, 6, v_currNamespace_1434_);
                lean_ctor_set(v___x_1445_, 7, v_openDecls_1435_);
                lean_ctor_set(v___x_1445_, 8, v_initHeartbeats_1436_);
                lean_ctor_set(v___x_1445_, 9, v_maxHeartbeats_1437_);
                lean_ctor_set(v___x_1445_, 10, v_quotContext_1438_);
                lean_ctor_set(v___x_1445_, 11, v_currMacroScope_1439_);
                lean_ctor_set(v___x_1445_, 12, v_cancelTk_x3f_1440_);
                lean_ctor_set(v___x_1445_, 13, v_inheritedTraceOptions_1442_);
                lean_ctor_set_uint8(
                    v___x_1445_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_1426_,
                );
                lean_ctor_set_uint8(
                    v___x_1445_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1441_,
                );
                v___x_1446_ = l_Lean_addAndCompile(
                    v___y_1422_,
                    v___y_1421_,
                    v___y_1425_,
                    v___x_1445_,
                    v___y_1443_,
                );
                if lean_obj_tag(v___x_1446_) == 0 {
                    lean_dec_ref_known(v___x_1446_, 1);
                    v___x_1447_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(
                        v___y_1429_,
                        v_checkMeta_1411_,
                        v___y_1423_,
                        v___y_1428_,
                        v___x_1445_,
                        v___y_1443_,
                    );
                    lean_dec(v___y_1443_);
                    lean_dec_ref_known(v___x_1445_, 14);
                    lean_dec(v___y_1428_);
                    lean_dec_ref(v___y_1423_);
                    return v___x_1447_;
                } else {
                    lean_dec_ref_known(v___x_1445_, 14);
                    lean_dec(v___y_1443_);
                    lean_dec(v___y_1429_);
                    lean_dec(v___y_1428_);
                    lean_dec_ref(v___y_1423_);
                    v_a_1448_ = lean_ctor_get(v___x_1446_, 0);
                    v_isSharedCheck_1455_ = (!lean_is_exclusive(v___x_1446_)) as u8;
                    if v_isSharedCheck_1455_ == 0 {
                        v___x_1450_ = v___x_1446_;
                        v_isShared_1451_ = v_isSharedCheck_1455_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1448_);
                        lean_dec(v___x_1446_);
                        v___x_1450_ = lean_box(0);
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
                    v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
                    v___x_1453_ = v_reuseFailAlloc_1454_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1453_;
            }
            4 => {
                v_fileName_1468_ = lean_ctor_get(v___y_1466_, 0);
                lean_inc_ref(v_fileName_1468_);
                v_fileMap_1469_ = lean_ctor_get(v___y_1466_, 1);
                lean_inc_ref(v_fileMap_1469_);
                v_currRecDepth_1470_ = lean_ctor_get(v___y_1466_, 3);
                lean_inc(v_currRecDepth_1470_);
                v_ref_1471_ = lean_ctor_get(v___y_1466_, 5);
                lean_inc(v_ref_1471_);
                v_currNamespace_1472_ = lean_ctor_get(v___y_1466_, 6);
                lean_inc(v_currNamespace_1472_);
                v_openDecls_1473_ = lean_ctor_get(v___y_1466_, 7);
                lean_inc(v_openDecls_1473_);
                v_initHeartbeats_1474_ = lean_ctor_get(v___y_1466_, 8);
                lean_inc(v_initHeartbeats_1474_);
                v_maxHeartbeats_1475_ = lean_ctor_get(v___y_1466_, 9);
                lean_inc(v_maxHeartbeats_1475_);
                v_quotContext_1476_ = lean_ctor_get(v___y_1466_, 10);
                lean_inc(v_quotContext_1476_);
                v_currMacroScope_1477_ = lean_ctor_get(v___y_1466_, 11);
                lean_inc(v_currMacroScope_1477_);
                v_cancelTk_x3f_1478_ = lean_ctor_get(v___y_1466_, 12);
                lean_inc(v_cancelTk_x3f_1478_);
                v_suppressElabErrors_1479_ = lean_ctor_get_uint8(
                    v___y_1466_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1480_ = lean_ctor_get(v___y_1466_, 13);
                lean_inc_ref(v_inheritedTraceOptions_1480_);
                lean_dec_ref(v___y_1466_);
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
                    v_env_1496_ = lean_ctor_get(v___x_1495_, 0);
                    v_nextMacroScope_1497_ = lean_ctor_get(v___x_1495_, 1);
                    v_ngen_1498_ = lean_ctor_get(v___x_1495_, 2);
                    v_auxDeclNGen_1499_ = lean_ctor_get(v___x_1495_, 3);
                    v_traceState_1500_ = lean_ctor_get(v___x_1495_, 4);
                    v_messages_1501_ = lean_ctor_get(v___x_1495_, 6);
                    v_infoState_1502_ = lean_ctor_get(v___x_1495_, 7);
                    v_snapshotTasks_1503_ = lean_ctor_get(v___x_1495_, 8);
                    v_isSharedCheck_1512_ = (!lean_is_exclusive(v___x_1495_)) as u8;
                    if v_isSharedCheck_1512_ == 0 {
                        v_unused_1513_ = lean_ctor_get(v___x_1495_, 5);
                        lean_dec(v_unused_1513_);
                        v___x_1505_ = v___x_1495_;
                        v_isShared_1506_ = v_isSharedCheck_1512_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_1503_);
                        lean_inc(v_infoState_1502_);
                        lean_inc(v_messages_1501_);
                        lean_inc(v_traceState_1500_);
                        lean_inc(v_auxDeclNGen_1499_);
                        lean_inc(v_ngen_1498_);
                        lean_inc(v_nextMacroScope_1497_);
                        lean_inc(v_env_1496_);
                        lean_dec(v___x_1495_);
                        v___x_1505_ = lean_box(0);
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
                lean_inc_ref(v___y_1484_);
                if v_isShared_1506_ == 0 {
                    lean_ctor_set(v___x_1505_, 5, v___y_1484_);
                    lean_ctor_set(v___x_1505_, 0, v___x_1507_);
                    v___x_1509_ = v___x_1505_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1507_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_nextMacroScope_1497_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_ngen_1498_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_auxDeclNGen_1499_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_traceState_1500_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 5, v___y_1484_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 6, v_messages_1501_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 7, v_infoState_1502_);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 8, v_snapshotTasks_1503_);
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
                v_fileName_1529_ = lean_ctor_get(v___y_1526_, 0);
                v_fileMap_1530_ = lean_ctor_get(v___y_1526_, 1);
                v_currRecDepth_1531_ = lean_ctor_get(v___y_1526_, 3);
                v_ref_1532_ = lean_ctor_get(v___y_1526_, 5);
                v_currNamespace_1533_ = lean_ctor_get(v___y_1526_, 6);
                v_openDecls_1534_ = lean_ctor_get(v___y_1526_, 7);
                v_initHeartbeats_1535_ = lean_ctor_get(v___y_1526_, 8);
                v_maxHeartbeats_1536_ = lean_ctor_get(v___y_1526_, 9);
                v_quotContext_1537_ = lean_ctor_get(v___y_1526_, 10);
                v_currMacroScope_1538_ = lean_ctor_get(v___y_1526_, 11);
                v_cancelTk_x3f_1539_ = lean_ctor_get(v___y_1526_, 12);
                v_suppressElabErrors_1540_ = lean_ctor_get_uint8(
                    v___y_1526_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1541_ = lean_ctor_get(v___y_1526_, 13);
                v_isSharedCheck_1554_ = (!lean_is_exclusive(v___y_1526_)) as u8;
                if v_isSharedCheck_1554_ == 0 {
                    v_unused_1555_ = lean_ctor_get(v___y_1526_, 4);
                    lean_dec(v_unused_1555_);
                    v_unused_1556_ = lean_ctor_get(v___y_1526_, 2);
                    lean_dec(v_unused_1556_);
                    v___x_1543_ = v___y_1526_;
                    v_isShared_1544_ = v_isSharedCheck_1554_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_inheritedTraceOptions_1541_);
                    lean_inc(v_cancelTk_x3f_1539_);
                    lean_inc(v_currMacroScope_1538_);
                    lean_inc(v_quotContext_1537_);
                    lean_inc(v_maxHeartbeats_1536_);
                    lean_inc(v_initHeartbeats_1535_);
                    lean_inc(v_openDecls_1534_);
                    lean_inc(v_currNamespace_1533_);
                    lean_inc(v_ref_1532_);
                    lean_inc(v_currRecDepth_1531_);
                    lean_inc(v_fileMap_1530_);
                    lean_inc(v_fileName_1529_);
                    lean_dec(v___y_1526_);
                    v___x_1543_ = lean_box(0);
                    v_isShared_1544_ = v_isSharedCheck_1554_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_env_1545_ = lean_ctor_get(v___x_1528_, 0);
                lean_inc_ref(v_env_1545_);
                lean_dec(v___x_1528_);
                v___x_1546_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(
                    v___y_1525_,
                    v___y_1522_,
                );
                lean_inc_ref(v_inheritedTraceOptions_1541_);
                lean_inc(v_cancelTk_x3f_1539_);
                lean_inc(v_currMacroScope_1538_);
                lean_inc(v_quotContext_1537_);
                lean_inc(v_maxHeartbeats_1536_);
                lean_inc(v_initHeartbeats_1535_);
                lean_inc(v_openDecls_1534_);
                lean_inc(v_currNamespace_1533_);
                lean_inc(v_ref_1532_);
                lean_inc(v_currRecDepth_1531_);
                lean_inc_ref(v___y_1525_);
                lean_inc_ref(v_fileMap_1530_);
                lean_inc_ref(v_fileName_1529_);
                if v_isShared_1544_ == 0 {
                    lean_ctor_set(v___x_1543_, 4, v___x_1546_);
                    lean_ctor_set(v___x_1543_, 2, v___y_1525_);
                    v___x_1548_ = v___x_1543_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_fileName_1529_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_fileMap_1530_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 2, v___y_1525_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_currRecDepth_1531_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 4, v___x_1546_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 5, v_ref_1532_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 6, v_currNamespace_1533_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 7, v_openDecls_1534_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 8, v_initHeartbeats_1535_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 9, v_maxHeartbeats_1536_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 10, v_quotContext_1537_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 11, v_currMacroScope_1538_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 12, v_cancelTk_x3f_1539_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 13, v_inheritedTraceOptions_1541_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1553_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1540_,
                    );
                    v___x_1548_ = v_reuseFailAlloc_1553_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                lean_ctor_set_uint8(
                    v___x_1548_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
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
                lean_dec_ref(v_env_1545_);
                if v___x_1552_ == 0 {
                    if v___x_1551_ == 0 {
                        lean_dec_ref(v___x_1548_);
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
                        lean_dec_ref(v_inheritedTraceOptions_1541_);
                        lean_dec(v_cancelTk_x3f_1539_);
                        lean_dec(v_currMacroScope_1538_);
                        lean_dec(v_quotContext_1537_);
                        lean_dec(v_maxHeartbeats_1536_);
                        lean_dec(v_initHeartbeats_1535_);
                        lean_dec(v_openDecls_1534_);
                        lean_dec(v_currNamespace_1533_);
                        lean_dec(v_ref_1532_);
                        lean_dec(v_currRecDepth_1531_);
                        lean_dec_ref(v_fileMap_1530_);
                        lean_dec_ref(v_fileName_1529_);
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
                    lean_dec_ref(v_inheritedTraceOptions_1541_);
                    lean_dec(v_cancelTk_x3f_1539_);
                    lean_dec(v_currMacroScope_1538_);
                    lean_dec(v_quotContext_1537_);
                    lean_dec(v_maxHeartbeats_1536_);
                    lean_dec(v_initHeartbeats_1535_);
                    lean_dec(v_openDecls_1534_);
                    lean_dec(v_currNamespace_1533_);
                    lean_dec(v_ref_1532_);
                    lean_dec(v_currRecDepth_1531_);
                    lean_dec_ref(v_fileMap_1530_);
                    lean_dec_ref(v_fileName_1529_);
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
                    v_env_1573_ = lean_ctor_get(v___x_1572_, 0);
                    v_nextMacroScope_1574_ = lean_ctor_get(v___x_1572_, 1);
                    v_ngen_1575_ = lean_ctor_get(v___x_1572_, 2);
                    v_auxDeclNGen_1576_ = lean_ctor_get(v___x_1572_, 3);
                    v_traceState_1577_ = lean_ctor_get(v___x_1572_, 4);
                    v_messages_1578_ = lean_ctor_get(v___x_1572_, 6);
                    v_infoState_1579_ = lean_ctor_get(v___x_1572_, 7);
                    v_snapshotTasks_1580_ = lean_ctor_get(v___x_1572_, 8);
                    v_isSharedCheck_1589_ = (!lean_is_exclusive(v___x_1572_)) as u8;
                    if v_isSharedCheck_1589_ == 0 {
                        v_unused_1590_ = lean_ctor_get(v___x_1572_, 5);
                        lean_dec(v_unused_1590_);
                        v___x_1582_ = v___x_1572_;
                        v_isShared_1583_ = v_isSharedCheck_1589_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_1580_);
                        lean_inc(v_infoState_1579_);
                        lean_inc(v_messages_1578_);
                        lean_inc(v_traceState_1577_);
                        lean_inc(v_auxDeclNGen_1576_);
                        lean_inc(v_ngen_1575_);
                        lean_inc(v_nextMacroScope_1574_);
                        lean_inc(v_env_1573_);
                        lean_dec(v___x_1572_);
                        v___x_1582_ = lean_box(0);
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
                lean_inc_ref(v___y_1561_);
                if v_isShared_1583_ == 0 {
                    lean_ctor_set(v___x_1582_, 5, v___y_1561_);
                    lean_ctor_set(v___x_1582_, 0, v___x_1584_);
                    v___x_1586_ = v___x_1582_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1584_);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_nextMacroScope_1574_);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_ngen_1575_);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 3, v_auxDeclNGen_1576_);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 4, v_traceState_1577_);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 5, v___y_1561_);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 6, v_messages_1578_);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 7, v_infoState_1579_);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 8, v_snapshotTasks_1580_);
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
                v_fileName_1605_ = lean_ctor_get(v___y_1602_, 0);
                v_fileMap_1606_ = lean_ctor_get(v___y_1602_, 1);
                v_currRecDepth_1607_ = lean_ctor_get(v___y_1602_, 3);
                v_ref_1608_ = lean_ctor_get(v___y_1602_, 5);
                v_currNamespace_1609_ = lean_ctor_get(v___y_1602_, 6);
                v_openDecls_1610_ = lean_ctor_get(v___y_1602_, 7);
                v_initHeartbeats_1611_ = lean_ctor_get(v___y_1602_, 8);
                v_maxHeartbeats_1612_ = lean_ctor_get(v___y_1602_, 9);
                v_quotContext_1613_ = lean_ctor_get(v___y_1602_, 10);
                v_currMacroScope_1614_ = lean_ctor_get(v___y_1602_, 11);
                v_cancelTk_x3f_1615_ = lean_ctor_get(v___y_1602_, 12);
                v_suppressElabErrors_1616_ = lean_ctor_get_uint8(
                    v___y_1602_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1617_ = lean_ctor_get(v___y_1602_, 13);
                v_isSharedCheck_1631_ = (!lean_is_exclusive(v___y_1602_)) as u8;
                if v_isSharedCheck_1631_ == 0 {
                    v_unused_1632_ = lean_ctor_get(v___y_1602_, 4);
                    lean_dec(v_unused_1632_);
                    v_unused_1633_ = lean_ctor_get(v___y_1602_, 2);
                    lean_dec(v_unused_1633_);
                    v___x_1619_ = v___y_1602_;
                    v_isShared_1620_ = v_isSharedCheck_1631_;
                    state = 15;
                    continue;
                } else {
                    lean_inc(v_inheritedTraceOptions_1617_);
                    lean_inc(v_cancelTk_x3f_1615_);
                    lean_inc(v_currMacroScope_1614_);
                    lean_inc(v_quotContext_1613_);
                    lean_inc(v_maxHeartbeats_1612_);
                    lean_inc(v_initHeartbeats_1611_);
                    lean_inc(v_openDecls_1610_);
                    lean_inc(v_currNamespace_1609_);
                    lean_inc(v_ref_1608_);
                    lean_inc(v_currRecDepth_1607_);
                    lean_inc(v_fileMap_1606_);
                    lean_inc(v_fileName_1605_);
                    lean_dec(v___y_1602_);
                    v___x_1619_ = lean_box(0);
                    v_isShared_1620_ = v_isSharedCheck_1631_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_env_1621_ = lean_ctor_get(v___x_1604_, 0);
                lean_inc_ref(v_env_1621_);
                lean_dec(v___x_1604_);
                v___x_1622_ = l_Lean_maxRecDepth;
                v___x_1623_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(
                    v___y_1599_,
                    v___x_1622_,
                );
                lean_inc_ref(v___y_1599_);
                if v_isShared_1620_ == 0 {
                    lean_ctor_set(v___x_1619_, 4, v___x_1623_);
                    lean_ctor_set(v___x_1619_, 2, v___y_1599_);
                    v___x_1625_ = v___x_1619_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_fileName_1605_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_fileMap_1606_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 2, v___y_1599_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_currRecDepth_1607_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 4, v___x_1623_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 5, v_ref_1608_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 6, v_currNamespace_1609_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 7, v_openDecls_1610_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 8, v_initHeartbeats_1611_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 9, v_maxHeartbeats_1612_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 10, v_quotContext_1613_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 11, v_currMacroScope_1614_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 12, v_cancelTk_x3f_1615_);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 13, v_inheritedTraceOptions_1617_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1630_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1616_,
                    );
                    v___x_1625_ = v_reuseFailAlloc_1630_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                lean_ctor_set_uint8(
                    v___x_1625_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
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
                lean_dec_ref(v_env_1621_);
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
                    v_env_1649_ = lean_ctor_get(v___x_1648_, 0);
                    v_nextMacroScope_1650_ = lean_ctor_get(v___x_1648_, 1);
                    v_ngen_1651_ = lean_ctor_get(v___x_1648_, 2);
                    v_auxDeclNGen_1652_ = lean_ctor_get(v___x_1648_, 3);
                    v_traceState_1653_ = lean_ctor_get(v___x_1648_, 4);
                    v_messages_1654_ = lean_ctor_get(v___x_1648_, 6);
                    v_infoState_1655_ = lean_ctor_get(v___x_1648_, 7);
                    v_snapshotTasks_1656_ = lean_ctor_get(v___x_1648_, 8);
                    v_isSharedCheck_1665_ = (!lean_is_exclusive(v___x_1648_)) as u8;
                    if v_isSharedCheck_1665_ == 0 {
                        v_unused_1666_ = lean_ctor_get(v___x_1648_, 5);
                        lean_dec(v_unused_1666_);
                        v___x_1658_ = v___x_1648_;
                        v_isShared_1659_ = v_isSharedCheck_1665_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_1656_);
                        lean_inc(v_infoState_1655_);
                        lean_inc(v_messages_1654_);
                        lean_inc(v_traceState_1653_);
                        lean_inc(v_auxDeclNGen_1652_);
                        lean_inc(v_ngen_1651_);
                        lean_inc(v_nextMacroScope_1650_);
                        lean_inc(v_env_1649_);
                        lean_dec(v___x_1648_);
                        v___x_1658_ = lean_box(0);
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
                lean_inc_ref(v___y_1636_);
                if v_isShared_1659_ == 0 {
                    lean_ctor_set(v___x_1658_, 5, v___y_1636_);
                    lean_ctor_set(v___x_1658_, 0, v___x_1660_);
                    v___x_1662_ = v___x_1658_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1660_);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_nextMacroScope_1650_);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_ngen_1651_);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_auxDeclNGen_1652_);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_traceState_1653_);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 5, v___y_1636_);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 6, v_messages_1654_);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 7, v_infoState_1655_);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 8, v_snapshotTasks_1656_);
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
                lean_inc(v___y_1675_);
                lean_inc_ref(v___y_1674_);
                lean_inc(v___y_1673_);
                lean_inc_ref(v___y_1672_);
                lean_inc_ref(v___y_1671_);
                v___x_1676_ = lean_infer_type(
                    v___y_1671_,
                    v___y_1672_,
                    v___y_1673_,
                    v___y_1674_,
                    v___y_1675_,
                );
                if lean_obj_tag(v___x_1676_) == 0 {
                    v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
                    lean_inc_n(v_a_1677_, 2);
                    lean_dec_ref_known(v___x_1676_, 1);
                    lean_inc(v___y_1675_);
                    lean_inc_ref(v___y_1674_);
                    lean_inc(v___y_1673_);
                    lean_inc_ref(v___y_1672_);
                    v___x_1678_ = lean_apply_6(
                        v_checkType_1412_,
                        v_a_1677_,
                        v___y_1672_,
                        v___y_1673_,
                        v___y_1674_,
                        v___y_1675_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1678_) == 0 {
                        lean_dec_ref_known(v___x_1678_, 1);
                        v___x_1679_ = lean_st_ref_take(v___y_1675_);
                        v_env_1680_ = lean_ctor_get(v___x_1679_, 0);
                        v_nextMacroScope_1681_ = lean_ctor_get(v___x_1679_, 1);
                        v_ngen_1682_ = lean_ctor_get(v___x_1679_, 2);
                        v_auxDeclNGen_1683_ = lean_ctor_get(v___x_1679_, 3);
                        v_traceState_1684_ = lean_ctor_get(v___x_1679_, 4);
                        v_messages_1685_ = lean_ctor_get(v___x_1679_, 6);
                        v_infoState_1686_ = lean_ctor_get(v___x_1679_, 7);
                        v_snapshotTasks_1687_ = lean_ctor_get(v___x_1679_, 8);
                        v_isSharedCheck_1741_ = (!lean_is_exclusive(v___x_1679_)) as u8;
                        if v_isSharedCheck_1741_ == 0 {
                            v_unused_1742_ = lean_ctor_get(v___x_1679_, 5);
                            lean_dec(v_unused_1742_);
                            v___x_1689_ = v___x_1679_;
                            v_isShared_1690_ = v_isSharedCheck_1741_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_1687_);
                            lean_inc(v_infoState_1686_);
                            lean_inc(v_messages_1685_);
                            lean_inc(v_traceState_1684_);
                            lean_inc(v_auxDeclNGen_1683_);
                            lean_inc(v_ngen_1682_);
                            lean_inc(v_nextMacroScope_1681_);
                            lean_inc(v_env_1680_);
                            lean_dec(v___x_1679_);
                            v___x_1689_ = lean_box(0);
                            v_isShared_1690_ = v_isSharedCheck_1741_;
                            state = 21;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1677_);
                        lean_dec(v___y_1675_);
                        lean_dec_ref(v___y_1674_);
                        lean_dec(v___y_1673_);
                        lean_dec_ref(v___y_1672_);
                        lean_dec_ref(v___y_1671_);
                        lean_dec(v___y_1670_);
                        lean_dec_ref(v___y_1668_);
                        v_a_1743_ = lean_ctor_get(v___x_1678_, 0);
                        v_isSharedCheck_1750_ = (!lean_is_exclusive(v___x_1678_)) as u8;
                        if v_isSharedCheck_1750_ == 0 {
                            v___x_1745_ = v___x_1678_;
                            v_isShared_1746_ = v_isSharedCheck_1750_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_1743_);
                            lean_dec(v___x_1678_);
                            v___x_1745_ = lean_box(0);
                            v_isShared_1746_ = v_isSharedCheck_1750_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_1675_);
                    lean_dec_ref(v___y_1674_);
                    lean_dec(v___y_1673_);
                    lean_dec_ref(v___y_1672_);
                    lean_dec_ref(v___y_1671_);
                    lean_dec(v___y_1670_);
                    lean_dec_ref(v___y_1668_);
                    lean_dec_ref(v_checkType_1412_);
                    v_a_1751_ = lean_ctor_get(v___x_1676_, 0);
                    v_isSharedCheck_1758_ = (!lean_is_exclusive(v___x_1676_)) as u8;
                    if v_isSharedCheck_1758_ == 0 {
                        v___x_1753_ = v___x_1676_;
                        v_isShared_1754_ = v_isSharedCheck_1758_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_a_1751_);
                        lean_dec(v___x_1676_);
                        v___x_1753_ = lean_box(0);
                        v_isShared_1754_ = v_isSharedCheck_1758_;
                        state = 29;
                        continue;
                    }
                }
            }
            21 => {
                v___x_1691_ = lean_array_to_list(v___y_1668_);
                lean_inc_n(v___y_1670_, 3);
                v___x_1692_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1692_, 0, v___y_1670_);
                lean_ctor_set(v___x_1692_, 1, v___x_1691_);
                lean_ctor_set(v___x_1692_, 2, v_a_1677_);
                lean_inc(v___y_1669_);
                v___x_1693_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1693_, 0, v___y_1670_);
                lean_ctor_set(v___x_1693_, 1, v___y_1669_);
                v___x_1694_ = l_Lean_markMeta(v_env_1680_, v___y_1670_);
                v___x_1695_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2,
                );
                if v_isShared_1690_ == 0 {
                    lean_ctor_set(v___x_1689_, 5, v___x_1695_);
                    lean_ctor_set(v___x_1689_, 0, v___x_1694_);
                    v___x_1697_ = v___x_1689_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1694_);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_nextMacroScope_1681_);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_ngen_1682_);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_auxDeclNGen_1683_);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_traceState_1684_);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 5, v___x_1695_);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 6, v_messages_1685_);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 7, v_infoState_1686_);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 8, v_snapshotTasks_1687_);
                    v___x_1697_ = v_reuseFailAlloc_1740_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1698_ = lean_st_ref_set(v___y_1675_, v___x_1697_);
                v___x_1699_ = lean_st_ref_take(v___y_1673_);
                v_mctx_1700_ = lean_ctor_get(v___x_1699_, 0);
                v_zetaDeltaFVarIds_1701_ = lean_ctor_get(v___x_1699_, 2);
                v_postponed_1702_ = lean_ctor_get(v___x_1699_, 3);
                v_diag_1703_ = lean_ctor_get(v___x_1699_, 4);
                v_isSharedCheck_1738_ = (!lean_is_exclusive(v___x_1699_)) as u8;
                if v_isSharedCheck_1738_ == 0 {
                    v_unused_1739_ = lean_ctor_get(v___x_1699_, 1);
                    lean_dec(v_unused_1739_);
                    v___x_1705_ = v___x_1699_;
                    v_isShared_1706_ = v_isSharedCheck_1738_;
                    state = 23;
                    continue;
                } else {
                    lean_inc(v_diag_1703_);
                    lean_inc(v_postponed_1702_);
                    lean_inc(v_zetaDeltaFVarIds_1701_);
                    lean_inc(v_mctx_1700_);
                    lean_dec(v___x_1699_);
                    v___x_1705_ = lean_box(0);
                    v_isShared_1706_ = v_isSharedCheck_1738_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_1707_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3,
                );
                if v_isShared_1706_ == 0 {
                    lean_ctor_set(v___x_1705_, 1, v___x_1707_);
                    v___x_1709_ = v___x_1705_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_mctx_1700_);
                    lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1707_);
                    lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_zetaDeltaFVarIds_1701_);
                    lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_postponed_1702_);
                    lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_diag_1703_);
                    v___x_1709_ = v_reuseFailAlloc_1737_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_1710_ = lean_st_ref_set(v___y_1673_, v___x_1709_);
                v___x_1711_ = lean_st_ref_get(v___y_1675_);
                v_env_1712_ = lean_ctor_get(v___x_1711_, 0);
                lean_inc_ref(v_env_1712_);
                lean_dec(v___x_1711_);
                v_checked_1713_ = lean_ctor_get(v_env_1712_, 2);
                lean_inc_ref(v_checked_1713_);
                lean_dec_ref(v_env_1712_);
                v___x_1714_ = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4;
                v___x_1715_ = l_Lean_traceBlock___redArg(
                    v___x_1714_,
                    v_checked_1713_,
                    v___y_1674_,
                    v___y_1675_,
                );
                if lean_obj_tag(v___x_1715_) == 0 {
                    lean_dec_ref_known(v___x_1715_, 1);
                    v___x_1716_ = lean_st_ref_get(v___y_1675_);
                    v_options_1717_ = lean_ctor_get(v___y_1674_, 2);
                    v_env_1718_ = lean_ctor_get(v___x_1716_, 0);
                    lean_inc_ref(v_env_1718_);
                    lean_dec(v___x_1716_);
                    v___x_1719_ = lean_box(0);
                    v___x_1720_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v___x_1720_, 0, v___x_1692_);
                    lean_ctor_set(v___x_1720_, 1, v___y_1671_);
                    lean_ctor_set(v___x_1720_, 2, v___x_1719_);
                    lean_ctor_set(v___x_1720_, 3, v___x_1693_);
                    lean_ctor_set_uint8(
                        v___x_1720_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_safety_1413_,
                    );
                    v___x_1721_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1721_, 0, v___x_1720_);
                    v___x_1722_ = 1;
                    v___x_1723_ = 0;
                    v___x_1724_ = l_Lean_Elab_async;
                    lean_inc_ref(v_options_1717_);
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
                    lean_dec_ref(v_env_1718_);
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
                    lean_dec_ref_known(v___x_1693_, 2);
                    lean_dec_ref_known(v___x_1692_, 3);
                    lean_dec(v___y_1675_);
                    lean_dec_ref(v___y_1674_);
                    lean_dec(v___y_1673_);
                    lean_dec_ref(v___y_1672_);
                    lean_dec_ref(v___y_1671_);
                    lean_dec(v___y_1670_);
                    v_a_1729_ = lean_ctor_get(v___x_1715_, 0);
                    v_isSharedCheck_1736_ = (!lean_is_exclusive(v___x_1715_)) as u8;
                    if v_isSharedCheck_1736_ == 0 {
                        v___x_1731_ = v___x_1715_;
                        v_isShared_1732_ = v_isSharedCheck_1736_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_1729_);
                        lean_dec(v___x_1715_);
                        v___x_1731_ = lean_box(0);
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
                    v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
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
                    v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
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
                    v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
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
                if lean_obj_tag(v___x_1766_) == 0 {
                    v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
                    lean_inc(v_a_1767_);
                    lean_dec_ref_known(v___x_1766_, 1);
                    v___x_1768_ =
                        l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(
                            v_value_1414_,
                            v___y_1761_,
                        );
                    if lean_obj_tag(v___x_1768_) == 0 {
                        v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
                        lean_inc_n(v_a_1769_, 2);
                        lean_dec_ref_known(v___x_1768_, 1);
                        v_env_1770_ = lean_ctor_get(v___x_1764_, 0);
                        lean_inc_ref(v_env_1770_);
                        lean_dec(v___x_1764_);
                        v___x_1771_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once
                            ),
                            _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10,
                        );
                        v___x_1772_ = l_Lean_collectLevelParams(v___x_1771_, v_a_1769_);
                        v_params_1773_ = lean_ctor_get(v___x_1772_, 2);
                        lean_inc_ref(v_params_1773_);
                        lean_dec_ref(v___x_1772_);
                        v___x_1774_ = l_Lean_mkPrivateName(v_env_1770_, v_a_1767_);
                        lean_dec_ref(v_env_1770_);
                        v___x_1775_ = lean_box(0);
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
                            v___x_1777_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once
                                ),
                                _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12,
                            );
                            lean_inc(v_a_1769_);
                            v___x_1778_ = l_Lean_indentExpr(v_a_1769_);
                            v___x_1779_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1779_, 0, v___x_1777_);
                            lean_ctor_set(v___x_1779_, 1, v___x_1778_);
                            v___x_1780_ =
                                l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(
                                    v___x_1779_,
                                    v___y_1760_,
                                    v___y_1761_,
                                    v___y_1762_,
                                    v___y_1763_,
                                );
                            if lean_obj_tag(v___x_1780_) == 0 {
                                lean_dec_ref_known(v___x_1780_, 1);
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
                                lean_dec(v___x_1774_);
                                lean_dec_ref(v_params_1773_);
                                lean_dec(v_a_1769_);
                                lean_dec(v___y_1763_);
                                lean_dec_ref(v___y_1762_);
                                lean_dec(v___y_1761_);
                                lean_dec_ref(v___y_1760_);
                                lean_dec_ref(v_checkType_1412_);
                                v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
                                v_isSharedCheck_1788_ = (!lean_is_exclusive(v___x_1780_)) as u8;
                                if v_isSharedCheck_1788_ == 0 {
                                    v___x_1783_ = v___x_1780_;
                                    v_isShared_1784_ = v_isSharedCheck_1788_;
                                    state = 32;
                                    continue;
                                } else {
                                    lean_inc(v_a_1781_);
                                    lean_dec(v___x_1780_);
                                    v___x_1783_ = lean_box(0);
                                    v_isShared_1784_ = v_isSharedCheck_1788_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_1767_);
                        lean_dec(v___x_1764_);
                        lean_dec(v___y_1763_);
                        lean_dec_ref(v___y_1762_);
                        lean_dec(v___y_1761_);
                        lean_dec_ref(v___y_1760_);
                        lean_dec_ref(v_checkType_1412_);
                        v_a_1789_ = lean_ctor_get(v___x_1768_, 0);
                        v_isSharedCheck_1796_ = (!lean_is_exclusive(v___x_1768_)) as u8;
                        if v_isSharedCheck_1796_ == 0 {
                            v___x_1791_ = v___x_1768_;
                            v_isShared_1792_ = v_isSharedCheck_1796_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_a_1789_);
                            lean_dec(v___x_1768_);
                            v___x_1791_ = lean_box(0);
                            v_isShared_1792_ = v_isSharedCheck_1796_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1764_);
                    lean_dec(v___y_1763_);
                    lean_dec_ref(v___y_1762_);
                    lean_dec(v___y_1761_);
                    lean_dec_ref(v___y_1760_);
                    lean_dec_ref(v_value_1414_);
                    lean_dec_ref(v_checkType_1412_);
                    v_a_1797_ = lean_ctor_get(v___x_1766_, 0);
                    v_isSharedCheck_1804_ = (!lean_is_exclusive(v___x_1766_)) as u8;
                    if v_isSharedCheck_1804_ == 0 {
                        v___x_1799_ = v___x_1766_;
                        v_isShared_1800_ = v_isSharedCheck_1804_;
                        state = 36;
                        continue;
                    } else {
                        lean_inc(v_a_1797_);
                        lean_dec(v___x_1766_);
                        v___x_1799_ = lean_box(0);
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
                    v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
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
                    v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
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
                    v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
                    v___x_1802_ = v_reuseFailAlloc_1803_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1802_;
            }
            38 => {
                v___x_1814_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2,
                );
                v___x_1815_ = lean_alloc_ctor(0, 9, (0) as u32);
                lean_ctor_set(v___x_1815_, 0, v___y_1813_);
                lean_ctor_set(v___x_1815_, 1, v_nextMacroScope_1806_);
                lean_ctor_set(v___x_1815_, 2, v_ngen_1807_);
                lean_ctor_set(v___x_1815_, 3, v_auxDeclNGen_1808_);
                lean_ctor_set(v___x_1815_, 4, v_traceState_1809_);
                lean_ctor_set(v___x_1815_, 5, v___x_1814_);
                lean_ctor_set(v___x_1815_, 6, v_messages_1810_);
                lean_ctor_set(v___x_1815_, 7, v_infoState_1811_);
                lean_ctor_set(v___x_1815_, 8, v_snapshotTasks_1812_);
                v___x_1816_ = lean_st_ref_set(v___y_1418_, v___x_1815_);
                v___x_1817_ = lean_st_ref_take(v___y_1416_);
                v_mctx_1818_ = lean_ctor_get(v___x_1817_, 0);
                v_zetaDeltaFVarIds_1819_ = lean_ctor_get(v___x_1817_, 2);
                v_postponed_1820_ = lean_ctor_get(v___x_1817_, 3);
                v_diag_1821_ = lean_ctor_get(v___x_1817_, 4);
                v_isSharedCheck_1830_ = (!lean_is_exclusive(v___x_1817_)) as u8;
                if v_isSharedCheck_1830_ == 0 {
                    v_unused_1831_ = lean_ctor_get(v___x_1817_, 1);
                    lean_dec(v_unused_1831_);
                    v___x_1823_ = v___x_1817_;
                    v_isShared_1824_ = v_isSharedCheck_1830_;
                    state = 39;
                    continue;
                } else {
                    lean_inc(v_diag_1821_);
                    lean_inc(v_postponed_1820_);
                    lean_inc(v_zetaDeltaFVarIds_1819_);
                    lean_inc(v_mctx_1818_);
                    lean_dec(v___x_1817_);
                    v___x_1823_ = lean_box(0);
                    v_isShared_1824_ = v_isSharedCheck_1830_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                v___x_1825_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3,
                );
                if v_isShared_1824_ == 0 {
                    lean_ctor_set(v___x_1823_, 1, v___x_1825_);
                    v___x_1827_ = v___x_1823_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_mctx_1818_);
                    lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___x_1825_);
                    lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_zetaDeltaFVarIds_1819_);
                    lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_postponed_1820_);
                    lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_diag_1821_);
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
                v_env_1835_ = lean_ctor_get(v___x_1834_, 0);
                lean_inc_ref_n(v_env_1835_, 2);
                v_nextMacroScope_1836_ = lean_ctor_get(v___x_1834_, 1);
                lean_inc(v_nextMacroScope_1836_);
                v_ngen_1837_ = lean_ctor_get(v___x_1834_, 2);
                lean_inc_ref(v_ngen_1837_);
                v_auxDeclNGen_1838_ = lean_ctor_get(v___x_1834_, 3);
                lean_inc_ref(v_auxDeclNGen_1838_);
                v_traceState_1839_ = lean_ctor_get(v___x_1834_, 4);
                lean_inc_ref(v_traceState_1839_);
                v_messages_1840_ = lean_ctor_get(v___x_1834_, 6);
                lean_inc_ref(v_messages_1840_);
                v_infoState_1841_ = lean_ctor_get(v___x_1834_, 7);
                lean_inc_ref(v_infoState_1841_);
                v_snapshotTasks_1842_ = lean_ctor_get(v___x_1834_, 8);
                lean_inc_ref(v_snapshotTasks_1842_);
                lean_dec(v___x_1834_);
                v___x_1843_ = l_Lean_Environment_importEnv_x3f(v_env_1835_);
                if lean_obj_tag(v___x_1843_) == 0 {
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
                    lean_dec_ref(v_env_1835_);
                    v_val_1844_ = lean_ctor_get(v___x_1843_, 0);
                    lean_inc(v_val_1844_);
                    lean_dec_ref_known(v___x_1843_, 1);
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
    mut v_checkMeta_1853_: *mut LeanObject,
    mut v_checkType_1854_: *mut LeanObject,
    mut v_safety_1855_: *mut LeanObject,
    mut v_value_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checkMeta_boxed_1862_: u8 = 0;
    let mut v_safety_boxed_1863_: u8 = 0;
    let mut v_res_1864_: *mut LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1862_ = (lean_unbox(v_checkMeta_1853_) as u8);
    v_safety_boxed_1863_ = (lean_unbox(v_safety_1855_) as u8);
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
    mut v_env_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1879_: u8 = 0;
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut v_unused_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1902_: u8 = 0;
    let mut v_unused_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1869_ = lean_st_ref_take(v___y_1867_);
                v_nextMacroScope_1870_ = lean_ctor_get(v___x_1869_, 1);
                v_ngen_1871_ = lean_ctor_get(v___x_1869_, 2);
                v_auxDeclNGen_1872_ = lean_ctor_get(v___x_1869_, 3);
                v_traceState_1873_ = lean_ctor_get(v___x_1869_, 4);
                v_messages_1874_ = lean_ctor_get(v___x_1869_, 6);
                v_infoState_1875_ = lean_ctor_get(v___x_1869_, 7);
                v_snapshotTasks_1876_ = lean_ctor_get(v___x_1869_, 8);
                v_isSharedCheck_1902_ = (!lean_is_exclusive(v___x_1869_)) as u8;
                if v_isSharedCheck_1902_ == 0 {
                    v_unused_1903_ = lean_ctor_get(v___x_1869_, 5);
                    lean_dec(v_unused_1903_);
                    v_unused_1904_ = lean_ctor_get(v___x_1869_, 0);
                    lean_dec(v_unused_1904_);
                    v___x_1878_ = v___x_1869_;
                    v_isShared_1879_ = v_isSharedCheck_1902_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1876_);
                    lean_inc(v_infoState_1875_);
                    lean_inc(v_messages_1874_);
                    lean_inc(v_traceState_1873_);
                    lean_inc(v_auxDeclNGen_1872_);
                    lean_inc(v_ngen_1871_);
                    lean_inc(v_nextMacroScope_1870_);
                    lean_dec(v___x_1869_);
                    v___x_1878_ = lean_box(0);
                    v_isShared_1879_ = v_isSharedCheck_1902_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1880_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2,
                );
                if v_isShared_1879_ == 0 {
                    lean_ctor_set(v___x_1878_, 5, v___x_1880_);
                    lean_ctor_set(v___x_1878_, 0, v_env_1865_);
                    v___x_1882_ = v___x_1878_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_env_1865_);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_nextMacroScope_1870_);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_ngen_1871_);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_auxDeclNGen_1872_);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_traceState_1873_);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 5, v___x_1880_);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 6, v_messages_1874_);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 7, v_infoState_1875_);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 8, v_snapshotTasks_1876_);
                    v___x_1882_ = v_reuseFailAlloc_1901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1883_ = lean_st_ref_set(v___y_1867_, v___x_1882_);
                v___x_1884_ = lean_st_ref_take(v___y_1866_);
                v_mctx_1885_ = lean_ctor_get(v___x_1884_, 0);
                v_zetaDeltaFVarIds_1886_ = lean_ctor_get(v___x_1884_, 2);
                v_postponed_1887_ = lean_ctor_get(v___x_1884_, 3);
                v_diag_1888_ = lean_ctor_get(v___x_1884_, 4);
                v_isSharedCheck_1899_ = (!lean_is_exclusive(v___x_1884_)) as u8;
                if v_isSharedCheck_1899_ == 0 {
                    v_unused_1900_ = lean_ctor_get(v___x_1884_, 1);
                    lean_dec(v_unused_1900_);
                    v___x_1890_ = v___x_1884_;
                    v_isShared_1891_ = v_isSharedCheck_1899_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_1888_);
                    lean_inc(v_postponed_1887_);
                    lean_inc(v_zetaDeltaFVarIds_1886_);
                    lean_inc(v_mctx_1885_);
                    lean_dec(v___x_1884_);
                    v___x_1890_ = lean_box(0);
                    v_isShared_1891_ = v_isSharedCheck_1899_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1892_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3,
                );
                if v_isShared_1891_ == 0 {
                    lean_ctor_set(v___x_1890_, 1, v___x_1892_);
                    v___x_1894_ = v___x_1890_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_mctx_1885_);
                    lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1892_);
                    lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_zetaDeltaFVarIds_1886_);
                    lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_postponed_1887_);
                    lean_ctor_set(v_reuseFailAlloc_1898_, 4, v_diag_1888_);
                    v___x_1894_ = v_reuseFailAlloc_1898_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1895_ = lean_st_ref_set(v___y_1866_, v___x_1894_);
                v___x_1896_ = lean_box(0);
                v___x_1897_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1897_, 0, v___x_1896_);
                return v___x_1897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(
    mut v_env_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1909_: *mut LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_1905_, v___y_1906_, v___y_1907_);
    lean_dec(v___y_1907_);
    lean_dec(v___y_1906_);
    return v_res_1909_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(
    mut v_env_1910_: *mut LeanObject,
    mut v_x_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
    mut v___y_1915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut v_unused_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v_unused_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1917_ = lean_st_ref_get(v___y_1915_);
                v_env_1918_ = lean_ctor_get(v___x_1917_, 0);
                lean_inc_ref(v_env_1918_);
                lean_dec(v___x_1917_);
                v___x_1930_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_1910_, v___y_1913_, v___y_1915_);
                lean_dec_ref(v___x_1930_);
                lean_inc(v___y_1915_);
                lean_inc_ref(v___y_1914_);
                lean_inc(v___y_1913_);
                lean_inc_ref(v___y_1912_);
                v___x_1931_ = lean_apply_5(
                    v_x_1911_,
                    v___y_1912_,
                    v___y_1913_,
                    v___y_1914_,
                    v___y_1915_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1931_) == 0 {
                    v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
                    lean_inc(v_a_1932_);
                    lean_dec_ref_known(v___x_1931_, 1);
                    v___x_1933_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_1918_, v___y_1913_, v___y_1915_);
                    v_isSharedCheck_1940_ = (!lean_is_exclusive(v___x_1933_)) as u8;
                    if v_isSharedCheck_1940_ == 0 {
                        v_unused_1941_ = lean_ctor_get(v___x_1933_, 0);
                        lean_dec(v_unused_1941_);
                        v___x_1935_ = v___x_1933_;
                        v_isShared_1936_ = v_isSharedCheck_1940_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_1933_);
                        v___x_1935_ = lean_box(0);
                        v_isShared_1936_ = v_isSharedCheck_1940_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_1942_ = lean_ctor_get(v___x_1931_, 0);
                    lean_inc(v_a_1942_);
                    lean_dec_ref_known(v___x_1931_, 1);
                    v_a_1920_ = v_a_1942_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1921_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_1918_, v___y_1913_, v___y_1915_);
                v_isSharedCheck_1928_ = (!lean_is_exclusive(v___x_1921_)) as u8;
                if v_isSharedCheck_1928_ == 0 {
                    v_unused_1929_ = lean_ctor_get(v___x_1921_, 0);
                    lean_dec(v_unused_1929_);
                    v___x_1923_ = v___x_1921_;
                    v_isShared_1924_ = v_isSharedCheck_1928_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_1921_);
                    v___x_1923_ = lean_box(0);
                    v_isShared_1924_ = v_isSharedCheck_1928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1924_ == 0 {
                    lean_ctor_set_tag(v___x_1923_, 1);
                    lean_ctor_set(v___x_1923_, 0, v_a_1920_);
                    v___x_1926_ = v___x_1923_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1920_);
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
                    lean_ctor_set(v___x_1935_, 0, v_a_1932_);
                    v___x_1938_ = v___x_1935_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1932_);
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
    mut v_env_1943_: *mut LeanObject,
    mut v_x_1944_: *mut LeanObject,
    mut v___y_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
    mut v___y_1947_: *mut LeanObject,
    mut v___y_1948_: *mut LeanObject,
    mut v___y_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1950_: *mut LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(
        v_env_1943_,
        v_x_1944_,
        v___y_1945_,
        v___y_1946_,
        v___y_1947_,
        v___y_1948_,
    );
    lean_dec(v___y_1948_);
    lean_dec_ref(v___y_1947_);
    lean_dec(v___y_1946_);
    lean_dec_ref(v___y_1945_);
    return v_res_1950_;
}
pub unsafe fn l_Lean_Meta_evalExprCore___redArg(
    mut v_value_1951_: *mut LeanObject,
    mut v_checkType_1952_: *mut LeanObject,
    mut v_safety_1953_: u8,
    mut v_checkMeta_1954_: u8,
    mut v_a_1955_: *mut LeanObject,
    mut v_a_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    v___x_1960_ = lean_st_ref_get(v_a_1958_);
    v_env_1961_ = lean_ctor_get(v___x_1960_, 0);
    lean_inc_ref(v_env_1961_);
    lean_dec(v___x_1960_);
    v___x_1962_ = lean_box((v_checkMeta_1954_) as usize);
    v___x_1963_ = lean_box((v_safety_1953_) as usize);
    v___f_1964_ = lean_alloc_closure(
        l_Lean_Meta_evalExprCore___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_1964_, 0, v___x_1962_);
    lean_closure_set(v___f_1964_, 1, v_checkType_1952_);
    lean_closure_set(v___f_1964_, 2, v___x_1963_);
    lean_closure_set(v___f_1964_, 3, v_value_1951_);
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
    mut v_value_1967_: *mut LeanObject,
    mut v_checkType_1968_: *mut LeanObject,
    mut v_safety_1969_: *mut LeanObject,
    mut v_checkMeta_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
    mut v_a_1974_: *mut LeanObject,
    mut v_a_1975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_safety_boxed_1976_: u8 = 0;
    let mut v_checkMeta_boxed_1977_: u8 = 0;
    let mut v_res_1978_: *mut LeanObject = core::ptr::null_mut();
    v_safety_boxed_1976_ = (lean_unbox(v_safety_1969_) as u8);
    v_checkMeta_boxed_1977_ = (lean_unbox(v_checkMeta_1970_) as u8);
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
    lean_dec(v_a_1974_);
    lean_dec_ref(v_a_1973_);
    lean_dec(v_a_1972_);
    lean_dec_ref(v_a_1971_);
    return v_res_1978_;
}
pub unsafe fn l_Lean_Meta_evalExprCore(
    mut v_00_u03b1_1979_: *mut LeanObject,
    mut v_value_1980_: *mut LeanObject,
    mut v_checkType_1981_: *mut LeanObject,
    mut v_safety_1982_: u8,
    mut v_checkMeta_1983_: u8,
    mut v_a_1984_: *mut LeanObject,
    mut v_a_1985_: *mut LeanObject,
    mut v_a_1986_: *mut LeanObject,
    mut v_a_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1990_: *mut LeanObject,
    mut v_value_1991_: *mut LeanObject,
    mut v_checkType_1992_: *mut LeanObject,
    mut v_safety_1993_: *mut LeanObject,
    mut v_checkMeta_1994_: *mut LeanObject,
    mut v_a_1995_: *mut LeanObject,
    mut v_a_1996_: *mut LeanObject,
    mut v_a_1997_: *mut LeanObject,
    mut v_a_1998_: *mut LeanObject,
    mut v_a_1999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_safety_boxed_2000_: u8 = 0;
    let mut v_checkMeta_boxed_2001_: u8 = 0;
    let mut v_res_2002_: *mut LeanObject = core::ptr::null_mut();
    v_safety_boxed_2000_ = (lean_unbox(v_safety_1993_) as u8);
    v_checkMeta_boxed_2001_ = (lean_unbox(v_checkMeta_1994_) as u8);
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
    lean_dec(v_a_1998_);
    lean_dec_ref(v_a_1997_);
    lean_dec(v_a_1996_);
    lean_dec_ref(v_a_1995_);
    return v_res_2002_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(
    mut v_00_u03b1_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    v___x_2009_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
    return v___x_2009_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(
    mut v_00_u03b1_2010_: *mut LeanObject,
    mut v___y_2011_: *mut LeanObject,
    mut v___y_2012_: *mut LeanObject,
    mut v___y_2013_: *mut LeanObject,
    mut v___y_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2016_: *mut LeanObject = core::ptr::null_mut();
    v_res_2016_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
    lean_dec(v___y_2014_);
    lean_dec_ref(v___y_2013_);
    lean_dec(v___y_2012_);
    lean_dec_ref(v___y_2011_);
    return v_res_2016_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(
    mut v_00_u03b1_2017_: *mut LeanObject,
    mut v_constName_2018_: *mut LeanObject,
    mut v_checkMeta_2019_: u8,
    mut v___y_2020_: *mut LeanObject,
    mut v___y_2021_: *mut LeanObject,
    mut v___y_2022_: *mut LeanObject,
    mut v___y_2023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2026_: *mut LeanObject,
    mut v_constName_2027_: *mut LeanObject,
    mut v_checkMeta_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
    mut v___y_2030_: *mut LeanObject,
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
    mut v___y_2033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checkMeta_boxed_2034_: u8 = 0;
    let mut v_res_2035_: *mut LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_2034_ = (lean_unbox(v_checkMeta_2028_) as u8);
    v_res_2035_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(
        v_00_u03b1_2026_,
        v_constName_2027_,
        v_checkMeta_boxed_2034_,
        v___y_2029_,
        v___y_2030_,
        v___y_2031_,
        v___y_2032_,
    );
    lean_dec(v___y_2032_);
    lean_dec_ref(v___y_2031_);
    lean_dec(v___y_2030_);
    lean_dec_ref(v___y_2029_);
    return v_res_2035_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(
    mut v_00_u03b1_2036_: *mut LeanObject,
    mut v_msg_2037_: *mut LeanObject,
    mut v___y_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2044_: *mut LeanObject,
    mut v_msg_2045_: *mut LeanObject,
    mut v___y_2046_: *mut LeanObject,
    mut v___y_2047_: *mut LeanObject,
    mut v___y_2048_: *mut LeanObject,
    mut v___y_2049_: *mut LeanObject,
    mut v___y_2050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2051_: *mut LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(
        v_00_u03b1_2044_,
        v_msg_2045_,
        v___y_2046_,
        v___y_2047_,
        v___y_2048_,
        v___y_2049_,
    );
    lean_dec(v___y_2049_);
    lean_dec_ref(v___y_2048_);
    lean_dec(v___y_2047_);
    lean_dec_ref(v___y_2046_);
    return v_res_2051_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(
    mut v_env_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    v___x_2058_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_2052_, v___y_2054_, v___y_2056_);
    return v___x_2058_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(
    mut v_env_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2065_: *mut LeanObject = core::ptr::null_mut();
    v_res_2065_ =
        l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(
            v_env_2059_,
            v___y_2060_,
            v___y_2061_,
            v___y_2062_,
            v___y_2063_,
        );
    lean_dec(v___y_2063_);
    lean_dec_ref(v___y_2062_);
    lean_dec(v___y_2061_);
    lean_dec_ref(v___y_2060_);
    return v_res_2065_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(
    mut v_00_u03b1_2066_: *mut LeanObject,
    mut v_env_2067_: *mut LeanObject,
    mut v_x_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
    mut v___y_2070_: *mut LeanObject,
    mut v___y_2071_: *mut LeanObject,
    mut v___y_2072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2075_: *mut LeanObject,
    mut v_env_2076_: *mut LeanObject,
    mut v_x_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
    mut v___y_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2083_: *mut LeanObject = core::ptr::null_mut();
    v_res_2083_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(
        v_00_u03b1_2075_,
        v_env_2076_,
        v_x_2077_,
        v___y_2078_,
        v___y_2079_,
        v___y_2080_,
        v___y_2081_,
    );
    lean_dec(v___y_2081_);
    lean_dec_ref(v___y_2080_);
    lean_dec(v___y_2079_);
    lean_dec_ref(v___y_2078_);
    return v_res_2083_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(
    mut v_00_u03b1_2084_: *mut LeanObject,
    mut v_x_2085_: *mut LeanObject,
    mut v___y_2086_: *mut LeanObject,
    mut v___y_2087_: *mut LeanObject,
    mut v___y_2088_: *mut LeanObject,
    mut v___y_2089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    v___x_2091_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
    return v___x_2091_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(
    mut v_00_u03b1_2092_: *mut LeanObject,
    mut v_x_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2099_: *mut LeanObject = core::ptr::null_mut();
    v_res_2099_ =
        l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(
            v_00_u03b1_2092_,
            v_x_2093_,
            v___y_2094_,
            v___y_2095_,
            v___y_2096_,
            v___y_2097_,
        );
    lean_dec(v___y_2097_);
    lean_dec_ref(v___y_2096_);
    lean_dec(v___y_2095_);
    lean_dec_ref(v___y_2094_);
    return v_res_2099_;
}
pub unsafe fn _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    v___x_2101_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0;
    v___x_2102_ = l_Lean_stringToMessageData(v___x_2101_);
    return v___x_2102_;
}
pub unsafe fn l_Lean_Meta_evalExpr_x27___redArg___lam__0(
    mut v_typeName_2103_: *mut LeanObject,
    mut v_type_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
    mut v___y_2108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_a_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2110_) == 0 {
                    v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
                    v_isSharedCheck_2124_ = (!lean_is_exclusive(v___x_2110_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v___x_2113_ = v___x_2110_;
                        v_isShared_2114_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2111_);
                        lean_dec(v___x_2110_);
                        v___x_2113_ = lean_box(0);
                        v_isShared_2114_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2125_ = lean_ctor_get(v___x_2110_, 0);
                    v_isSharedCheck_2132_ = (!lean_is_exclusive(v___x_2110_)) as u8;
                    if v_isSharedCheck_2132_ == 0 {
                        v___x_2127_ = v___x_2110_;
                        v_isShared_2128_ = v_isSharedCheck_2132_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2125_);
                        lean_dec(v___x_2110_);
                        v___x_2127_ = lean_box(0);
                        v_isShared_2128_ = v_isSharedCheck_2132_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2115_ = l_Lean_Expr_isConstOf(v_a_2111_, v_typeName_2103_);
                if v___x_2115_ == 0 {
                    lean_del_object(v___x_2113_);
                    v___x_2116_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1,
                    );
                    v___x_2117_ = l_Lean_indentExpr(v_a_2111_);
                    v___x_2118_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2118_, 0, v___x_2116_);
                    lean_ctor_set(v___x_2118_, 1, v___x_2117_);
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
                    lean_dec(v_a_2111_);
                    v___x_2120_ = lean_box(0);
                    if v_isShared_2114_ == 0 {
                        lean_ctor_set(v___x_2113_, 0, v___x_2120_);
                        v___x_2122_ = v___x_2113_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
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
                    v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
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
    mut v_typeName_2133_: *mut LeanObject,
    mut v_type_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
    mut v___y_2137_: *mut LeanObject,
    mut v___y_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2140_: *mut LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(
        v_typeName_2133_,
        v_type_2134_,
        v___y_2135_,
        v___y_2136_,
        v___y_2137_,
        v___y_2138_,
    );
    lean_dec(v___y_2138_);
    lean_dec_ref(v___y_2137_);
    lean_dec(v___y_2136_);
    lean_dec_ref(v___y_2135_);
    lean_dec(v_typeName_2133_);
    return v_res_2140_;
}
pub unsafe fn l_Lean_Meta_evalExpr_x27___redArg(
    mut v_typeName_2141_: *mut LeanObject,
    mut v_value_2142_: *mut LeanObject,
    mut v_safety_2143_: u8,
    mut v_checkMeta_2144_: u8,
    mut v_a_2145_: *mut LeanObject,
    mut v_a_2146_: *mut LeanObject,
    mut v_a_2147_: *mut LeanObject,
    mut v_a_2148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    v___f_2150_ = lean_alloc_closure(
        l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_2150_, 0, v_typeName_2141_);
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
    mut v_typeName_2152_: *mut LeanObject,
    mut v_value_2153_: *mut LeanObject,
    mut v_safety_2154_: *mut LeanObject,
    mut v_checkMeta_2155_: *mut LeanObject,
    mut v_a_2156_: *mut LeanObject,
    mut v_a_2157_: *mut LeanObject,
    mut v_a_2158_: *mut LeanObject,
    mut v_a_2159_: *mut LeanObject,
    mut v_a_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_safety_boxed_2161_: u8 = 0;
    let mut v_checkMeta_boxed_2162_: u8 = 0;
    let mut v_res_2163_: *mut LeanObject = core::ptr::null_mut();
    v_safety_boxed_2161_ = (lean_unbox(v_safety_2154_) as u8);
    v_checkMeta_boxed_2162_ = (lean_unbox(v_checkMeta_2155_) as u8);
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
    lean_dec(v_a_2159_);
    lean_dec_ref(v_a_2158_);
    lean_dec(v_a_2157_);
    lean_dec_ref(v_a_2156_);
    return v_res_2163_;
}
pub unsafe fn l_Lean_Meta_evalExpr_x27(
    mut v_00_u03b1_2164_: *mut LeanObject,
    mut v_typeName_2165_: *mut LeanObject,
    mut v_value_2166_: *mut LeanObject,
    mut v_safety_2167_: u8,
    mut v_checkMeta_2168_: u8,
    mut v_a_2169_: *mut LeanObject,
    mut v_a_2170_: *mut LeanObject,
    mut v_a_2171_: *mut LeanObject,
    mut v_a_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2175_: *mut LeanObject,
    mut v_typeName_2176_: *mut LeanObject,
    mut v_value_2177_: *mut LeanObject,
    mut v_safety_2178_: *mut LeanObject,
    mut v_checkMeta_2179_: *mut LeanObject,
    mut v_a_2180_: *mut LeanObject,
    mut v_a_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
    mut v_a_2183_: *mut LeanObject,
    mut v_a_2184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_safety_boxed_2185_: u8 = 0;
    let mut v_checkMeta_boxed_2186_: u8 = 0;
    let mut v_res_2187_: *mut LeanObject = core::ptr::null_mut();
    v_safety_boxed_2185_ = (lean_unbox(v_safety_2178_) as u8);
    v_checkMeta_boxed_2186_ = (lean_unbox(v_checkMeta_2179_) as u8);
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
    lean_dec(v_a_2183_);
    lean_dec_ref(v_a_2182_);
    lean_dec(v_a_2181_);
    lean_dec_ref(v_a_2180_);
    return v_res_2187_;
}
pub unsafe fn _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    v___x_2191_ = l_Lean_Meta_evalExpr___redArg___lam__0___closed__1;
    v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
    return v___x_2192_;
}
pub unsafe fn l_Lean_Meta_evalExpr___redArg___lam__0(
    mut v_expectedType_2193_: *mut LeanObject,
    mut v_type_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
    mut v___y_2198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2204_: u8 = 0;
    let mut v___x_2205_: u8 = 0;
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2220_: u8 = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v_a_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_expectedType_2193_);
                lean_inc_ref(v_type_2194_);
                v___x_2200_ = l_Lean_Meta_isExprDefEq(
                    v_type_2194_,
                    v_expectedType_2193_,
                    v___y_2195_,
                    v___y_2196_,
                    v___y_2197_,
                    v___y_2198_,
                );
                if lean_obj_tag(v___x_2200_) == 0 {
                    v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
                    v_isSharedCheck_2225_ = (!lean_is_exclusive(v___x_2200_)) as u8;
                    if v_isSharedCheck_2225_ == 0 {
                        v___x_2203_ = v___x_2200_;
                        v_isShared_2204_ = v_isSharedCheck_2225_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2201_);
                        lean_dec(v___x_2200_);
                        v___x_2203_ = lean_box(0);
                        v_isShared_2204_ = v_isSharedCheck_2225_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_2194_);
                    lean_dec_ref(v_expectedType_2193_);
                    v_a_2226_ = lean_ctor_get(v___x_2200_, 0);
                    v_isSharedCheck_2233_ = (!lean_is_exclusive(v___x_2200_)) as u8;
                    if v_isSharedCheck_2233_ == 0 {
                        v___x_2228_ = v___x_2200_;
                        v_isShared_2229_ = v_isSharedCheck_2233_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2226_);
                        lean_dec(v___x_2200_);
                        v___x_2228_ = lean_box(0);
                        v_isShared_2229_ = v_isSharedCheck_2233_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2205_ = (lean_unbox(v_a_2201_) as u8);
                lean_dec(v_a_2201_);
                if v___x_2205_ == 0 {
                    lean_del_object(v___x_2203_);
                    v___x_2206_ = lean_box(0);
                    v___x_2207_ = l_Lean_Meta_evalExpr___redArg___lam__0___closed__0;
                    v___x_2208_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(
                        v_type_2194_,
                        v_expectedType_2193_,
                        v___x_2206_,
                        v___x_2207_,
                    );
                    if lean_obj_tag(v___x_2208_) == 0 {
                        v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
                        lean_inc(v_a_2209_);
                        lean_dec_ref_known(v___x_2208_, 1);
                        v___x_2210_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_evalExpr___redArg___lam__0___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once
                            ),
                            _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2,
                        );
                        v___x_2211_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2211_, 0, v___x_2210_);
                        lean_ctor_set(v___x_2211_, 1, v_a_2209_);
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
                        v_a_2213_ = lean_ctor_get(v___x_2208_, 0);
                        v_isSharedCheck_2220_ = (!lean_is_exclusive(v___x_2208_)) as u8;
                        if v_isSharedCheck_2220_ == 0 {
                            v___x_2215_ = v___x_2208_;
                            v_isShared_2216_ = v_isSharedCheck_2220_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2213_);
                            lean_dec(v___x_2208_);
                            v___x_2215_ = lean_box(0);
                            v_isShared_2216_ = v_isSharedCheck_2220_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_2194_);
                    lean_dec_ref(v_expectedType_2193_);
                    v___x_2221_ = lean_box(0);
                    if v_isShared_2204_ == 0 {
                        lean_ctor_set(v___x_2203_, 0, v___x_2221_);
                        v___x_2223_ = v___x_2203_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
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
                    v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
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
                    v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
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
    mut v_expectedType_2234_: *mut LeanObject,
    mut v_type_2235_: *mut LeanObject,
    mut v___y_2236_: *mut LeanObject,
    mut v___y_2237_: *mut LeanObject,
    mut v___y_2238_: *mut LeanObject,
    mut v___y_2239_: *mut LeanObject,
    mut v___y_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2241_: *mut LeanObject = core::ptr::null_mut();
    v_res_2241_ = l_Lean_Meta_evalExpr___redArg___lam__0(
        v_expectedType_2234_,
        v_type_2235_,
        v___y_2236_,
        v___y_2237_,
        v___y_2238_,
        v___y_2239_,
    );
    lean_dec(v___y_2239_);
    lean_dec_ref(v___y_2238_);
    lean_dec(v___y_2237_);
    lean_dec_ref(v___y_2236_);
    return v_res_2241_;
}
pub unsafe fn l_Lean_Meta_evalExpr___redArg(
    mut v_expectedType_2242_: *mut LeanObject,
    mut v_value_2243_: *mut LeanObject,
    mut v_safety_2244_: u8,
    mut v_checkMeta_2245_: u8,
    mut v_a_2246_: *mut LeanObject,
    mut v_a_2247_: *mut LeanObject,
    mut v_a_2248_: *mut LeanObject,
    mut v_a_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    v___f_2251_ = lean_alloc_closure(
        l_Lean_Meta_evalExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_2251_, 0, v_expectedType_2242_);
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
    mut v_expectedType_2253_: *mut LeanObject,
    mut v_value_2254_: *mut LeanObject,
    mut v_safety_2255_: *mut LeanObject,
    mut v_checkMeta_2256_: *mut LeanObject,
    mut v_a_2257_: *mut LeanObject,
    mut v_a_2258_: *mut LeanObject,
    mut v_a_2259_: *mut LeanObject,
    mut v_a_2260_: *mut LeanObject,
    mut v_a_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_safety_boxed_2262_: u8 = 0;
    let mut v_checkMeta_boxed_2263_: u8 = 0;
    let mut v_res_2264_: *mut LeanObject = core::ptr::null_mut();
    v_safety_boxed_2262_ = (lean_unbox(v_safety_2255_) as u8);
    v_checkMeta_boxed_2263_ = (lean_unbox(v_checkMeta_2256_) as u8);
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
    lean_dec(v_a_2260_);
    lean_dec_ref(v_a_2259_);
    lean_dec(v_a_2258_);
    lean_dec_ref(v_a_2257_);
    return v_res_2264_;
}
pub unsafe fn l_Lean_Meta_evalExpr(
    mut v_00_u03b1_2265_: *mut LeanObject,
    mut v_expectedType_2266_: *mut LeanObject,
    mut v_value_2267_: *mut LeanObject,
    mut v_safety_2268_: u8,
    mut v_checkMeta_2269_: u8,
    mut v_a_2270_: *mut LeanObject,
    mut v_a_2271_: *mut LeanObject,
    mut v_a_2272_: *mut LeanObject,
    mut v_a_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2276_: *mut LeanObject,
    mut v_expectedType_2277_: *mut LeanObject,
    mut v_value_2278_: *mut LeanObject,
    mut v_safety_2279_: *mut LeanObject,
    mut v_checkMeta_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_safety_boxed_2286_: u8 = 0;
    let mut v_checkMeta_boxed_2287_: u8 = 0;
    let mut v_res_2288_: *mut LeanObject = core::ptr::null_mut();
    v_safety_boxed_2286_ = (lean_unbox(v_safety_2279_) as u8);
    v_checkMeta_boxed_2287_ = (lean_unbox(v_checkMeta_2280_) as u8);
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
    lean_dec(v_a_2284_);
    lean_dec_ref(v_a_2283_);
    lean_dec(v_a_2282_);
    lean_dec_ref(v_a_2281_);
    return v_res_2288_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Eval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Check(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Eval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Eval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Check(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLevelParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Eval(builtin);
}

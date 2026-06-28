// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Basic
// Imports: Lean.Meta.Tactic.Replace Lean.Elab.Tactic.BuiltinTactic
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray2___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4,
    l_Lean_Name_mkStr5, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node5,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_closeUsingOrAdmit, l_Lean_Elab_Tactic_evalTactic,
    l_Lean_Elab_Tactic_evalTactic___boxed, l_Lean_Elab_Tactic_focus___redArg,
    l_Lean_Elab_Tactic_getGoals___redArg, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_getMainTarget, l_Lean_Elab_Tactic_getUnsolvedGoals,
    l_Lean_Elab_Tactic_mkInitialTacticInfo, l_Lean_Elab_Tactic_pruneSolvedGoals,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_saveTacticInfoForToken,
    l_Lean_Elab_Tactic_setGoals___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg, l_Lean_Elab_goalsToMessageData,
};
use crate::r#gen::Lean::Elab::Tactic::BuiltinTactic::{
    initialize_Lean_Elab_Tactic_BuiltinTactic, l_Lean_Elab_Tactic_evalFirst,
    l_Lean_Elab_Tactic_evalFirst___boxed, runtime_initialize_Lean_Elab_Tactic_BuiltinTactic,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_getFVarIds;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_getAppFn, l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isMVar,
    l_Lean_Expr_mdataExpr_x21, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_isLHSGoal_x3f, l_Lean_mkFVar, l_Lean_mkLHSGoalRaw,
    l_Lean_mkMVar,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_type};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkEq, l_Lean_Meta_mkEqMP, l_Lean_Meta_mkEqTrans,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MVarId_getKind,
    l_Lean_MVarId_setKind___redArg, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_getLocalDeclFromUserName, l_Lean_Meta_mkFreshExprMVar,
    l_Lean_Meta_saveState___redArg, l_Lean_Meta_sortFVarIds___redArg,
};
use crate::r#gen::Lean::Meta::MatchUtil::l_Lean_Meta_matchEq_x3f;
use crate::r#gen::Lean::Meta::Reduce::l_Lean_Meta_reduce;
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_clear;
use crate::r#gen::Lean::Meta::Tactic::Refl::l_Lean_MVarId_refl;
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    initialize_Lean_Meta_Tactic_Replace, l_Lean_MVarId_replace, l_Lean_MVarId_replaceTargetDefEq,
    l_Lean_MVarId_replaceTargetEq, runtime_initialize_Lean_Meta_Tactic_Replace,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_MVarId_inferInstance,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::Meta::Transform::l_Lean_Meta_zetaReduce;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_mod,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9,
    lean_apply_10, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_convert___closed__0_value: LeanStringObject<48> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 48,
        m_capacity: 48,
        m_length: 47,
        m_data: [
            84, 97, 99, 116, 105, 99, 32, 96, 99, 111, 110, 118, 96, 32, 102, 97, 105, 108, 101,
            100, 58, 32, 84, 104, 101, 114, 101, 32, 97, 114, 101, 32, 117, 110, 115, 111, 108,
            118, 101, 100, 32, 103, 111, 97, 108, 115, 10, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_convert___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_convert___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Conv_convert___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_convert___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0_value: LeanStringObject<68> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 68,
        m_capacity: 68,
        m_length: 67,
        m_data: [
            73, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 67, 111,
            110, 118, 101, 114, 115, 105, 111, 110, 45, 109, 111, 100, 101, 32, 116, 97, 99, 116,
            105, 99, 32, 102, 111, 117, 110, 100, 32, 97, 110, 32, 105, 110, 118, 97, 108, 105,
            100, 32, 96, 99, 111, 110, 118, 96, 32, 103, 111, 97, 108, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 104, 110, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value) as *mut LeanObject,5293136351122059060 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 87, 104, 110, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value) as *mut LeanObject,13077615496256101894 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 89 as usize) << 1) | 1) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 91 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 89 as usize) << 1) | 1) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 89 as usize) << 1) | 1) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 100, 117, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value) as *mut LeanObject,7650338142865358823 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 82, 101, 100, 117, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value) as *mut LeanObject,5873523377079161746 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 93 as usize) << 1) | 1) as *mut LeanObject,((( 49 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 95 as usize) << 1) | 1) as *mut LeanObject,((( 36 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value) as *mut LeanObject,((( 49 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value) as *mut LeanObject,((( 36 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 93 as usize) << 1) | 1) as *mut LeanObject,((( 53 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 93 as usize) << 1) | 1) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value) as *mut LeanObject,((( 53 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value) as *mut LeanObject,2162740105087520528 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 90, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value) as *mut LeanObject,399634079585865591 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 97 as usize) << 1) | 1) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 99 as usize) << 1) | 1) as *mut LeanObject,((( 40 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value) as *mut LeanObject,((( 40 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 97 as usize) << 1) | 1) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 97 as usize) << 1) | 1) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalClear___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [99, 108, 101, 97, 114, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalClear___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalClear___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalClear___closed__0_value)
                as *mut LeanObject,
            12526317070040649423 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalClear___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 67, 108, 101, 97, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value) as *mut LeanObject,18430213936427026185 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 111, 110, 118, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value) as *mut LeanObject,2194001538128159737 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 118, 97, 108, 67, 111, 110, 118, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value) as *mut LeanObject,5006757760655040425 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 109 as usize) << 1) | 1) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 110 as usize) << 1) | 1) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 109 as usize) << 1) | 1) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 109 as usize) << 1) | 1) as *mut LeanObject,((( 83 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value) as *mut LeanObject,((( 83 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [97, 108, 108, 71, 111, 97, 108, 115, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0_value)
            as *mut LeanObject,
        14131640301685195369 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [97, 108, 108, 95, 103, 111, 97, 108, 115, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value)
            as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value)
            as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value)
            as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 97, 114, 101, 110, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value)
            as *mut LeanObject,
        8689124066155232629 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [116, 97, 99, 116, 105, 99, 84, 114, 121, 95, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value
        ) as *mut LeanObject,
        10962186005905108258 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [116, 114, 121, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value
        ) as *mut LeanObject,
        6022092293134036165 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value
        ) as *mut LeanObject,
        3294379458557754569 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 102, 108, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 111, 110, 118, 83, 101, 113, 66, 114, 97, 99, 107, 101, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value) as *mut LeanObject,4863285515324763763 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 118, 97, 108, 67, 111, 110, 118, 83, 101, 113, 66, 114, 97, 99, 107, 101, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value) as *mut LeanObject,3209558272098469472 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 112 as usize) << 1) | 1) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 118 as usize) << 1) | 1) as *mut LeanObject,((( 64 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value) as *mut LeanObject,((( 64 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 112 as usize) << 1) | 1) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 112 as usize) << 1) | 1) as *mut LeanObject,((( 83 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value) as *mut LeanObject,((( 83 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [110, 101, 115, 116, 101, 100, 67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value) as *mut LeanObject,13793888648781409952 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 78, 101, 115, 116, 101, 100, 67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value) as *mut LeanObject,8122226020333733347 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 120 as usize) << 1) | 1) as *mut LeanObject,((( 53 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 121 as usize) << 1) | 1) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value) as *mut LeanObject,((( 53 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 120 as usize) << 1) | 1) as *mut LeanObject,((( 57 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 120 as usize) << 1) | 1) as *mut LeanObject,((( 71 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value) as *mut LeanObject,((( 57 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value) as *mut LeanObject,((( 71 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 110, 118, 83, 101, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value) as *mut LeanObject,4619875164071285194 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 118, 97, 108, 67, 111, 110, 118, 83, 101, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value) as *mut LeanObject,10699002042669531018 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 123 as usize) << 1) | 1) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 124 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 123 as usize) << 1) | 1) as *mut LeanObject,((( 54 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 123 as usize) << 1) | 1) as *mut LeanObject,((( 65 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value) as *mut LeanObject,((( 54 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value) as *mut LeanObject,((( 65 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 110, 118, 67, 111, 110, 118, 83, 101, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value) as *mut LeanObject,18300610594507675016 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 67, 111, 110, 118, 67, 111, 110, 118, 83, 101, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value) as *mut LeanObject,4577455594990651379 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 126 as usize) << 1) | 1) as *mut LeanObject,((( 54 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 129 as usize) << 1) | 1) as *mut LeanObject,((( 26 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value) as *mut LeanObject,((( 54 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value) as *mut LeanObject,((( 26 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 126 as usize) << 1) | 1) as *mut LeanObject,((( 58 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 126 as usize) << 1) | 1) as *mut LeanObject,((( 73 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value) as *mut LeanObject,((( 58 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value) as *mut LeanObject,((( 73 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value) as *mut LeanObject,4160726102902615044 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value) as *mut LeanObject,585080966098002 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 131 as usize) << 1) | 1) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 132 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 131 as usize) << 1) | 1) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 131 as usize) << 1) | 1) as *mut LeanObject,((( 61 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value) as *mut LeanObject,((( 61 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [110, 101, 115, 116, 101, 100, 84, 97, 99, 116, 105, 99, 67, 111, 114, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value) as *mut LeanObject,14672341133913102249 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 118, 97, 108, 78, 101, 115, 116, 101, 100, 84, 97, 99, 116, 105, 99, 67, 111, 114, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value) as *mut LeanObject,5814964435664386306 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 147 as usize) << 1) | 1) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 149 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 147 as usize) << 1) | 1) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 147 as usize) << 1) | 1) as *mut LeanObject,((( 83 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value) as *mut LeanObject,((( 83 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 101, 115, 116, 101, 100, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value) as *mut LeanObject,9934668988201376792 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 118, 97, 108, 78, 101, 115, 116, 101, 100, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value) as *mut LeanObject,5227818681740812151 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 151 as usize) << 1) | 1) as *mut LeanObject,((( 55 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 157 as usize) << 1) | 1) as *mut LeanObject,((( 43 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value) as *mut LeanObject,((( 55 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value) as *mut LeanObject,((( 43 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 151 as usize) << 1) | 1) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 151 as usize) << 1) | 1) as *mut LeanObject,((( 75 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value) as *mut LeanObject,((( 75 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 118, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value) as *mut LeanObject,3529167016356999086 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 67, 111, 110, 118, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value) as *mut LeanObject,15327872150820144598 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 159 as usize) << 1) | 1) as *mut LeanObject,((( 53 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 160 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value) as *mut LeanObject,((( 53 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 159 as usize) << 1) | 1) as *mut LeanObject,((( 57 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 159 as usize) << 1) | 1) as *mut LeanObject,((( 71 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value) as *mut LeanObject,((( 57 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value) as *mut LeanObject,((( 71 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value: LeanStringObject<5> =
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
        m_data: [99, 111, 110, 118, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalConv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value) as *mut LeanObject,
        8265518440499324864 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConv___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConv___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [59, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalConv___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConv___closed__3_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [61, 62, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalConv___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [112, 97, 116, 116, 101, 114, 110, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalConv___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value) as *mut LeanObject,
        3861856325106436923 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalConv___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalConv___closed__6_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Tactic_Conv_evalConv___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalConv___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalConv___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalConv___closed__8_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [97, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalConv___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalConv___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value) as *mut LeanObject,18123541720720748078 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 174 as usize) << 1) | 1) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 185 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 174 as usize) << 1) | 1) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 174 as usize) << 1) | 1) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Tactic_evalFirst___boxed as *const core::ffi::c_void, m_arity: 10, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 105, 114, 115, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value) as *mut LeanObject,17591797804533379362 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 70, 105, 114, 115, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value) as *mut LeanObject,3376717827333951819 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 187 as usize) << 1) | 1) as *mut LeanObject,((( 56 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 188 as usize) << 1) | 1) as *mut LeanObject,((( 18 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value) as *mut LeanObject,((( 56 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value) as *mut LeanObject,((( 18 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 187 as usize) << 1) | 1) as *mut LeanObject,((( 60 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 187 as usize) << 1) | 1) as *mut LeanObject,((( 69 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value) as *mut LeanObject,((( 60 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value) as *mut LeanObject,((( 69 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Conv_mkLHSGoal(
    mut v_e_4333_: *mut LeanObject,
    mut v_a_4334_: *mut LeanObject,
    mut v_a_4335_: *mut LeanObject,
    mut v_a_4336_: *mut LeanObject,
    mut v_a_4337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: u8 = 0;
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4351_: u8 = 0;
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4339_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1;
                v___x_4340_ = lean_unsigned_to_nat(3);
                v___x_4341_ = l_Lean_Expr_isAppOfArity(v_e_4333_, v___x_4339_, v___x_4340_);
                if v___x_4341_ == 0 {
                    lean_inc(v_a_4337_);
                    lean_inc_ref(v_a_4336_);
                    lean_inc(v_a_4335_);
                    lean_inc_ref(v_a_4334_);
                    v___x_4342_ = lean_whnf(v_e_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_);
                    if lean_obj_tag(v___x_4342_) == 0 {
                        v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
                        v_isSharedCheck_4351_ = (!lean_is_exclusive(v___x_4342_)) as u8;
                        if v_isSharedCheck_4351_ == 0 {
                            v___x_4345_ = v___x_4342_;
                            v_isShared_4346_ = v_isSharedCheck_4351_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4343_);
                            lean_dec(v___x_4342_);
                            v___x_4345_ = lean_box(0);
                            v_isShared_4346_ = v_isSharedCheck_4351_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_4342_;
                    }
                } else {
                    v___x_4352_ = l_Lean_mkLHSGoalRaw(v_e_4333_);
                    v___x_4353_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4353_, 0, v___x_4352_);
                    return v___x_4353_;
                }
            }
            1 => {
                v___x_4347_ = l_Lean_mkLHSGoalRaw(v_a_4343_);
                if v_isShared_4346_ == 0 {
                    lean_ctor_set(v___x_4345_, 0, v___x_4347_);
                    v___x_4349_ = v___x_4345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4347_);
                    v___x_4349_ = v_reuseFailAlloc_4350_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_mkLHSGoal___boxed(
    mut v_e_4354_: *mut LeanObject,
    mut v_a_4355_: *mut LeanObject,
    mut v_a_4356_: *mut LeanObject,
    mut v_a_4357_: *mut LeanObject,
    mut v_a_4358_: *mut LeanObject,
    mut v_a_4359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4360_: *mut LeanObject = core::ptr::null_mut();
    v_res_4360_ =
        l_Lean_Elab_Tactic_Conv_mkLHSGoal(v_e_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
    lean_dec(v_a_4358_);
    lean_dec_ref(v_a_4357_);
    lean_dec(v_a_4356_);
    lean_dec_ref(v_a_4355_);
    return v_res_4360_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_mkConvGoalFor(
    mut v_lhs_4361_: *mut LeanObject,
    mut v_tag_4362_: *mut LeanObject,
    mut v_a_4363_: *mut LeanObject,
    mut v_a_4364_: *mut LeanObject,
    mut v_a_4365_: *mut LeanObject,
    mut v_a_4366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4382_: u8 = 0;
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4387_: u8 = 0;
    let mut v_a_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4395_: u8 = 0;
    let mut v_a_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4399_: u8 = 0;
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4403_: u8 = 0;
    let mut v_a_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4407_: u8 = 0;
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4411_: u8 = 0;
    let mut v_a_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4415_: u8 = 0;
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_4366_);
                lean_inc_ref(v_a_4365_);
                lean_inc(v_a_4364_);
                lean_inc_ref(v_a_4363_);
                lean_inc_ref(v_lhs_4361_);
                v___x_4368_ =
                    lean_infer_type(v_lhs_4361_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
                if lean_obj_tag(v___x_4368_) == 0 {
                    v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
                    lean_inc(v_a_4369_);
                    lean_dec_ref_known(v___x_4368_, 1);
                    v___x_4370_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4370_, 0, v_a_4369_);
                    v___x_4371_ = 0;
                    v___x_4372_ = lean_box(0);
                    v___x_4373_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_4370_,
                        v___x_4371_,
                        v___x_4372_,
                        v_a_4363_,
                        v_a_4364_,
                        v_a_4365_,
                        v_a_4366_,
                    );
                    if lean_obj_tag(v___x_4373_) == 0 {
                        v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
                        lean_inc_n(v_a_4374_, 2);
                        lean_dec_ref_known(v___x_4373_, 1);
                        v___x_4375_ = l_Lean_Meta_mkEq(
                            v_lhs_4361_,
                            v_a_4374_,
                            v_a_4363_,
                            v_a_4364_,
                            v_a_4365_,
                            v_a_4366_,
                        );
                        if lean_obj_tag(v___x_4375_) == 0 {
                            v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
                            lean_inc(v_a_4376_);
                            lean_dec_ref_known(v___x_4375_, 1);
                            v___x_4377_ = l_Lean_mkLHSGoalRaw(v_a_4376_);
                            v___x_4378_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v___x_4377_,
                                v_tag_4362_,
                                v_a_4363_,
                                v_a_4364_,
                                v_a_4365_,
                                v_a_4366_,
                            );
                            if lean_obj_tag(v___x_4378_) == 0 {
                                v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
                                v_isSharedCheck_4387_ = (!lean_is_exclusive(v___x_4378_)) as u8;
                                if v_isSharedCheck_4387_ == 0 {
                                    v___x_4381_ = v___x_4378_;
                                    v_isShared_4382_ = v_isSharedCheck_4387_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4379_);
                                    lean_dec(v___x_4378_);
                                    v___x_4381_ = lean_box(0);
                                    v_isShared_4382_ = v_isSharedCheck_4387_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4374_);
                                v_a_4388_ = lean_ctor_get(v___x_4378_, 0);
                                v_isSharedCheck_4395_ = (!lean_is_exclusive(v___x_4378_)) as u8;
                                if v_isSharedCheck_4395_ == 0 {
                                    v___x_4390_ = v___x_4378_;
                                    v_isShared_4391_ = v_isSharedCheck_4395_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_4388_);
                                    lean_dec(v___x_4378_);
                                    v___x_4390_ = lean_box(0);
                                    v_isShared_4391_ = v_isSharedCheck_4395_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4374_);
                            lean_dec(v_tag_4362_);
                            v_a_4396_ = lean_ctor_get(v___x_4375_, 0);
                            v_isSharedCheck_4403_ = (!lean_is_exclusive(v___x_4375_)) as u8;
                            if v_isSharedCheck_4403_ == 0 {
                                v___x_4398_ = v___x_4375_;
                                v_isShared_4399_ = v_isSharedCheck_4403_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4396_);
                                lean_dec(v___x_4375_);
                                v___x_4398_ = lean_box(0);
                                v_isShared_4399_ = v_isSharedCheck_4403_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_tag_4362_);
                        lean_dec_ref(v_lhs_4361_);
                        v_a_4404_ = lean_ctor_get(v___x_4373_, 0);
                        v_isSharedCheck_4411_ = (!lean_is_exclusive(v___x_4373_)) as u8;
                        if v_isSharedCheck_4411_ == 0 {
                            v___x_4406_ = v___x_4373_;
                            v_isShared_4407_ = v_isSharedCheck_4411_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_4404_);
                            lean_dec(v___x_4373_);
                            v___x_4406_ = lean_box(0);
                            v_isShared_4407_ = v_isSharedCheck_4411_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_tag_4362_);
                    lean_dec_ref(v_lhs_4361_);
                    v_a_4412_ = lean_ctor_get(v___x_4368_, 0);
                    v_isSharedCheck_4419_ = (!lean_is_exclusive(v___x_4368_)) as u8;
                    if v_isSharedCheck_4419_ == 0 {
                        v___x_4414_ = v___x_4368_;
                        v_isShared_4415_ = v_isSharedCheck_4419_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4412_);
                        lean_dec(v___x_4368_);
                        v___x_4414_ = lean_box(0);
                        v_isShared_4415_ = v_isSharedCheck_4419_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4383_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4383_, 0, v_a_4374_);
                lean_ctor_set(v___x_4383_, 1, v_a_4379_);
                if v_isShared_4382_ == 0 {
                    lean_ctor_set(v___x_4381_, 0, v___x_4383_);
                    v___x_4385_ = v___x_4381_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
                    v___x_4385_ = v_reuseFailAlloc_4386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4385_;
            }
            3 => {
                if v_isShared_4391_ == 0 {
                    v___x_4393_ = v___x_4390_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
                    v___x_4393_ = v_reuseFailAlloc_4394_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4393_;
            }
            5 => {
                if v_isShared_4399_ == 0 {
                    v___x_4401_ = v___x_4398_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
                    v___x_4401_ = v_reuseFailAlloc_4402_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4401_;
            }
            7 => {
                if v_isShared_4407_ == 0 {
                    v___x_4409_ = v___x_4406_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
                    v___x_4409_ = v_reuseFailAlloc_4410_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4409_;
            }
            9 => {
                if v_isShared_4415_ == 0 {
                    v___x_4417_ = v___x_4414_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
                    v___x_4417_ = v_reuseFailAlloc_4418_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_mkConvGoalFor___boxed(
    mut v_lhs_4420_: *mut LeanObject,
    mut v_tag_4421_: *mut LeanObject,
    mut v_a_4422_: *mut LeanObject,
    mut v_a_4423_: *mut LeanObject,
    mut v_a_4424_: *mut LeanObject,
    mut v_a_4425_: *mut LeanObject,
    mut v_a_4426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4427_: *mut LeanObject = core::ptr::null_mut();
    v_res_4427_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(
        v_lhs_4420_,
        v_tag_4421_,
        v_a_4422_,
        v_a_4423_,
        v_a_4424_,
        v_a_4425_,
    );
    lean_dec(v_a_4425_);
    lean_dec_ref(v_a_4424_);
    lean_dec(v_a_4423_);
    lean_dec_ref(v_a_4422_);
    return v_res_4427_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_markAsConvGoal(
    mut v_mvarId_4428_: *mut LeanObject,
    mut v_a_4429_: *mut LeanObject,
    mut v_a_4430_: *mut LeanObject,
    mut v_a_4431_: *mut LeanObject,
    mut v_a_4432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4438_: u8 = 0;
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4448_: u8 = 0;
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4452_: u8 = 0;
    let mut v_a_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4460_: u8 = 0;
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4464_: u8 = 0;
    let mut v_a_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_4428_);
                v___x_4434_ = l_Lean_MVarId_getType(
                    v_mvarId_4428_,
                    v_a_4429_,
                    v_a_4430_,
                    v_a_4431_,
                    v_a_4432_,
                );
                if lean_obj_tag(v___x_4434_) == 0 {
                    v_a_4435_ = lean_ctor_get(v___x_4434_, 0);
                    v_isSharedCheck_4464_ = (!lean_is_exclusive(v___x_4434_)) as u8;
                    if v_isSharedCheck_4464_ == 0 {
                        v___x_4437_ = v___x_4434_;
                        v_isShared_4438_ = v_isSharedCheck_4464_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4435_);
                        lean_dec(v___x_4434_);
                        v___x_4437_ = lean_box(0);
                        v_isShared_4438_ = v_isSharedCheck_4464_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_4428_);
                    v_a_4465_ = lean_ctor_get(v___x_4434_, 0);
                    v_isSharedCheck_4472_ = (!lean_is_exclusive(v___x_4434_)) as u8;
                    if v_isSharedCheck_4472_ == 0 {
                        v___x_4467_ = v___x_4434_;
                        v_isShared_4468_ = v_isSharedCheck_4472_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4465_);
                        lean_dec(v___x_4434_);
                        v___x_4467_ = lean_box(0);
                        v_isShared_4468_ = v_isSharedCheck_4472_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4439_ = l_Lean_isLHSGoal_x3f(v_a_4435_);
                lean_dec(v_a_4435_);
                if lean_obj_tag(v___x_4439_) == 0 {
                    lean_del_object(v___x_4437_);
                    lean_inc(v_mvarId_4428_);
                    v___x_4440_ = l_Lean_MVarId_getType(
                        v_mvarId_4428_,
                        v_a_4429_,
                        v_a_4430_,
                        v_a_4431_,
                        v_a_4432_,
                    );
                    if lean_obj_tag(v___x_4440_) == 0 {
                        v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
                        lean_inc(v_a_4441_);
                        lean_dec_ref_known(v___x_4440_, 1);
                        v___x_4442_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal(
                            v_a_4441_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_,
                        );
                        if lean_obj_tag(v___x_4442_) == 0 {
                            v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
                            lean_inc(v_a_4443_);
                            lean_dec_ref_known(v___x_4442_, 1);
                            v___x_4444_ = l_Lean_MVarId_replaceTargetDefEq(
                                v_mvarId_4428_,
                                v_a_4443_,
                                v_a_4429_,
                                v_a_4430_,
                                v_a_4431_,
                                v_a_4432_,
                            );
                            return v___x_4444_;
                        } else {
                            lean_dec(v_mvarId_4428_);
                            v_a_4445_ = lean_ctor_get(v___x_4442_, 0);
                            v_isSharedCheck_4452_ = (!lean_is_exclusive(v___x_4442_)) as u8;
                            if v_isSharedCheck_4452_ == 0 {
                                v___x_4447_ = v___x_4442_;
                                v_isShared_4448_ = v_isSharedCheck_4452_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_4445_);
                                lean_dec(v___x_4442_);
                                v___x_4447_ = lean_box(0);
                                v_isShared_4448_ = v_isSharedCheck_4452_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_mvarId_4428_);
                        v_a_4453_ = lean_ctor_get(v___x_4440_, 0);
                        v_isSharedCheck_4460_ = (!lean_is_exclusive(v___x_4440_)) as u8;
                        if v_isSharedCheck_4460_ == 0 {
                            v___x_4455_ = v___x_4440_;
                            v_isShared_4456_ = v_isSharedCheck_4460_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4453_);
                            lean_dec(v___x_4440_);
                            v___x_4455_ = lean_box(0);
                            v_isShared_4456_ = v_isSharedCheck_4460_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_4439_, 1);
                    if v_isShared_4438_ == 0 {
                        lean_ctor_set(v___x_4437_, 0, v_mvarId_4428_);
                        v___x_4462_ = v___x_4437_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_mvarId_4428_);
                        v___x_4462_ = v_reuseFailAlloc_4463_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4448_ == 0 {
                    v___x_4450_ = v___x_4447_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
                    v___x_4450_ = v_reuseFailAlloc_4451_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4450_;
            }
            4 => {
                if v_isShared_4456_ == 0 {
                    v___x_4458_ = v___x_4455_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
                    v___x_4458_ = v_reuseFailAlloc_4459_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4458_;
            }
            6 => {
                return v___x_4462_;
            }
            7 => {
                if v_isShared_4468_ == 0 {
                    v___x_4470_ = v___x_4467_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
                    v___x_4470_ = v_reuseFailAlloc_4471_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_markAsConvGoal___boxed(
    mut v_mvarId_4473_: *mut LeanObject,
    mut v_a_4474_: *mut LeanObject,
    mut v_a_4475_: *mut LeanObject,
    mut v_a_4476_: *mut LeanObject,
    mut v_a_4477_: *mut LeanObject,
    mut v_a_4478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4479_: *mut LeanObject = core::ptr::null_mut();
    v_res_4479_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(
        v_mvarId_4473_,
        v_a_4474_,
        v_a_4475_,
        v_a_4476_,
        v_a_4477_,
    );
    lean_dec(v_a_4477_);
    lean_dec_ref(v_a_4476_);
    lean_dec(v_a_4475_);
    lean_dec_ref(v_a_4474_);
    return v_res_4479_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(
    mut v_e_4480_: *mut LeanObject,
    mut v___y_4481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4483_: u8 = 0;
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4497_: u8 = 0;
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4503_: u8 = 0;
    let mut v_unused_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4483_ = l_Lean_Expr_hasMVar(v_e_4480_);
                if v___x_4483_ == 0 {
                    v___x_4484_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4484_, 0, v_e_4480_);
                    return v___x_4484_;
                } else {
                    v___x_4485_ = lean_st_ref_get(v___y_4481_);
                    v_mctx_4486_ = lean_ctor_get(v___x_4485_, 0);
                    lean_inc_ref(v_mctx_4486_);
                    lean_dec(v___x_4485_);
                    v___x_4487_ = l_Lean_instantiateMVarsCore(v_mctx_4486_, v_e_4480_);
                    v_fst_4488_ = lean_ctor_get(v___x_4487_, 0);
                    lean_inc(v_fst_4488_);
                    v_snd_4489_ = lean_ctor_get(v___x_4487_, 1);
                    lean_inc(v_snd_4489_);
                    lean_dec_ref(v___x_4487_);
                    v___x_4490_ = lean_st_ref_take(v___y_4481_);
                    v_cache_4491_ = lean_ctor_get(v___x_4490_, 1);
                    v_zetaDeltaFVarIds_4492_ = lean_ctor_get(v___x_4490_, 2);
                    v_postponed_4493_ = lean_ctor_get(v___x_4490_, 3);
                    v_diag_4494_ = lean_ctor_get(v___x_4490_, 4);
                    v_isSharedCheck_4503_ = (!lean_is_exclusive(v___x_4490_)) as u8;
                    if v_isSharedCheck_4503_ == 0 {
                        v_unused_4504_ = lean_ctor_get(v___x_4490_, 0);
                        lean_dec(v_unused_4504_);
                        v___x_4496_ = v___x_4490_;
                        v_isShared_4497_ = v_isSharedCheck_4503_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4494_);
                        lean_inc(v_postponed_4493_);
                        lean_inc(v_zetaDeltaFVarIds_4492_);
                        lean_inc(v_cache_4491_);
                        lean_dec(v___x_4490_);
                        v___x_4496_ = lean_box(0);
                        v_isShared_4497_ = v_isSharedCheck_4503_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4497_ == 0 {
                    lean_ctor_set(v___x_4496_, 0, v_snd_4489_);
                    v___x_4499_ = v___x_4496_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_snd_4489_);
                    lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_cache_4491_);
                    lean_ctor_set(v_reuseFailAlloc_4502_, 2, v_zetaDeltaFVarIds_4492_);
                    lean_ctor_set(v_reuseFailAlloc_4502_, 3, v_postponed_4493_);
                    lean_ctor_set(v_reuseFailAlloc_4502_, 4, v_diag_4494_);
                    v___x_4499_ = v_reuseFailAlloc_4502_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4500_ = lean_st_ref_set(v___y_4481_, v___x_4499_);
                v___x_4501_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4501_, 0, v_fst_4488_);
                return v___x_4501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg___boxed(
    mut v_e_4505_: *mut LeanObject,
    mut v___y_4506_: *mut LeanObject,
    mut v___y_4507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4508_: *mut LeanObject = core::ptr::null_mut();
    v_res_4508_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(
        v_e_4505_,
        v___y_4506_,
    );
    lean_dec(v___y_4506_);
    return v_res_4508_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0(
    mut v_e_4509_: *mut LeanObject,
    mut v___y_4510_: *mut LeanObject,
    mut v___y_4511_: *mut LeanObject,
    mut v___y_4512_: *mut LeanObject,
    mut v___y_4513_: *mut LeanObject,
    mut v___y_4514_: *mut LeanObject,
    mut v___y_4515_: *mut LeanObject,
    mut v___y_4516_: *mut LeanObject,
    mut v___y_4517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    v___x_4519_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(
        v_e_4509_,
        v___y_4515_,
    );
    return v___x_4519_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___boxed(
    mut v_e_4520_: *mut LeanObject,
    mut v___y_4521_: *mut LeanObject,
    mut v___y_4522_: *mut LeanObject,
    mut v___y_4523_: *mut LeanObject,
    mut v___y_4524_: *mut LeanObject,
    mut v___y_4525_: *mut LeanObject,
    mut v___y_4526_: *mut LeanObject,
    mut v___y_4527_: *mut LeanObject,
    mut v___y_4528_: *mut LeanObject,
    mut v___y_4529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4530_: *mut LeanObject = core::ptr::null_mut();
    v_res_4530_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0(
        v_e_4520_,
        v___y_4521_,
        v___y_4522_,
        v___y_4523_,
        v___y_4524_,
        v___y_4525_,
        v___y_4526_,
        v___y_4527_,
        v___y_4528_,
    );
    lean_dec(v___y_4528_);
    lean_dec_ref(v___y_4527_);
    lean_dec(v___y_4526_);
    lean_dec_ref(v___y_4525_);
    lean_dec(v___y_4524_);
    lean_dec_ref(v___y_4523_);
    lean_dec(v___y_4522_);
    lean_dec_ref(v___y_4521_);
    return v_res_4530_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_convert___lam__0(
    mut v_____r_4531_: *mut LeanObject,
    mut v___y_4532_: *mut LeanObject,
    mut v___y_4533_: *mut LeanObject,
    mut v___y_4534_: *mut LeanObject,
    mut v___y_4535_: *mut LeanObject,
    mut v___y_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
    mut v___y_4538_: *mut LeanObject,
    mut v___y_4539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    v___x_4541_ = lean_box(0);
    v___x_4542_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4542_, 0, v___x_4541_);
    return v___x_4542_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_convert___lam__0___boxed(
    mut v_____r_4543_: *mut LeanObject,
    mut v___y_4544_: *mut LeanObject,
    mut v___y_4545_: *mut LeanObject,
    mut v___y_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
    mut v___y_4548_: *mut LeanObject,
    mut v___y_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
    mut v___y_4552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4553_: *mut LeanObject = core::ptr::null_mut();
    v_res_4553_ = l_Lean_Elab_Tactic_Conv_convert___lam__0(
        v_____r_4543_,
        v___y_4544_,
        v___y_4545_,
        v___y_4546_,
        v___y_4547_,
        v___y_4548_,
        v___y_4549_,
        v___y_4550_,
        v___y_4551_,
    );
    lean_dec(v___y_4551_);
    lean_dec_ref(v___y_4550_);
    lean_dec(v___y_4549_);
    lean_dec_ref(v___y_4548_);
    lean_dec(v___y_4547_);
    lean_dec_ref(v___y_4546_);
    lean_dec(v___y_4545_);
    lean_dec_ref(v___y_4544_);
    return v_res_4553_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(
    mut v_as_x27_4554_: *mut LeanObject,
    mut v_b_4555_: *mut LeanObject,
    mut v___y_4556_: *mut LeanObject,
    mut v___y_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4573_: u8 = 0;
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: u8 = 0;
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4580_: u8 = 0;
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: u8 = 0;
    let mut v___x_4587_: u8 = 0;
    let mut v_a_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4591_: u8 = 0;
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4595_: u8 = 0;
    let mut v___x_4596_: u8 = 0;
    let mut v___x_4597_: u8 = 0;
    let mut v_a_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4601_: u8 = 0;
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4554_) == 0 {
                    v___x_4561_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4561_, 0, v_b_4555_);
                    return v___x_4561_;
                } else {
                    v_head_4562_ = lean_ctor_get(v_as_x27_4554_, 0);
                    v_tail_4563_ = lean_ctor_get(v_as_x27_4554_, 1);
                    v___x_4564_ = l_Lean_Meta_saveState___redArg(v___y_4557_, v___y_4559_);
                    if lean_obj_tag(v___x_4564_) == 0 {
                        v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
                        lean_inc(v_a_4565_);
                        lean_dec_ref_known(v___x_4564_, 1);
                        v___x_4566_ = lean_box(0);
                        v___x_4576_ = 1;
                        lean_inc(v_head_4562_);
                        v___x_4577_ = l_Lean_MVarId_refl(
                            v_head_4562_,
                            v___x_4576_,
                            v___y_4556_,
                            v___y_4557_,
                            v___y_4558_,
                            v___y_4559_,
                        );
                        if lean_obj_tag(v___x_4577_) == 0 {
                            lean_dec(v_a_4565_);
                            v___y_4568_ = v___x_4577_;
                            state = 1;
                            continue;
                        } else {
                            v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
                            lean_inc(v_a_4578_);
                            v___x_4596_ = l_Lean_Exception_isInterrupt(v_a_4578_);
                            if v___x_4596_ == 0 {
                                v___x_4597_ = l_Lean_Exception_isRuntime(v_a_4578_);
                                v___y_4580_ = v___x_4597_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_a_4578_);
                                v___y_4580_ = v___x_4596_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4598_ = lean_ctor_get(v___x_4564_, 0);
                        v_isSharedCheck_4605_ = (!lean_is_exclusive(v___x_4564_)) as u8;
                        if v_isSharedCheck_4605_ == 0 {
                            v___x_4600_ = v___x_4564_;
                            v_isShared_4601_ = v_isSharedCheck_4605_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4598_);
                            lean_dec(v___x_4564_);
                            v___x_4600_ = lean_box(0);
                            v_isShared_4601_ = v_isSharedCheck_4605_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_4568_) == 0 {
                    lean_dec_ref_known(v___y_4568_, 1);
                    v_as_x27_4554_ = v_tail_4563_;
                    v_b_4555_ = v___x_4566_;
                    state = 0;
                    continue;
                } else {
                    return v___y_4568_;
                }
            }
            2 => {
                if v___y_4573_ == 0 {
                    lean_dec_ref(v___y_4572_);
                    v___x_4574_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_4571_,
                        v___y_4557_,
                        v___y_4559_,
                    );
                    lean_dec_ref(v___y_4571_);
                    if lean_obj_tag(v___x_4574_) == 0 {
                        lean_dec_ref_known(v___x_4574_, 1);
                        v_as_x27_4554_ = v_tail_4563_;
                        v_b_4555_ = v___x_4566_;
                        state = 0;
                        continue;
                    } else {
                        v___y_4568_ = v___x_4574_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_4571_);
                    v___y_4568_ = v___y_4572_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_4580_ == 0 {
                    lean_dec_ref_known(v___x_4577_, 1);
                    v___x_4581_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_4565_,
                        v___y_4557_,
                        v___y_4559_,
                    );
                    lean_dec(v_a_4565_);
                    if lean_obj_tag(v___x_4581_) == 0 {
                        lean_dec_ref_known(v___x_4581_, 1);
                        v___x_4582_ = l_Lean_Meta_saveState___redArg(v___y_4557_, v___y_4559_);
                        if lean_obj_tag(v___x_4582_) == 0 {
                            v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
                            lean_inc(v_a_4583_);
                            lean_dec_ref_known(v___x_4582_, 1);
                            lean_inc(v_head_4562_);
                            v___x_4584_ = l_Lean_MVarId_inferInstance(
                                v_head_4562_,
                                v___y_4556_,
                                v___y_4557_,
                                v___y_4558_,
                                v___y_4559_,
                            );
                            if lean_obj_tag(v___x_4584_) == 0 {
                                lean_dec(v_a_4583_);
                                v___y_4568_ = v___x_4584_;
                                state = 1;
                                continue;
                            } else {
                                v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
                                lean_inc(v_a_4585_);
                                v___x_4586_ = l_Lean_Exception_isInterrupt(v_a_4585_);
                                if v___x_4586_ == 0 {
                                    v___x_4587_ = l_Lean_Exception_isRuntime(v_a_4585_);
                                    v___y_4571_ = v_a_4583_;
                                    v___y_4572_ = v___x_4584_;
                                    v___y_4573_ = v___x_4587_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec(v_a_4585_);
                                    v___y_4571_ = v_a_4583_;
                                    v___y_4572_ = v___x_4584_;
                                    v___y_4573_ = v___x_4586_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4588_ = lean_ctor_get(v___x_4582_, 0);
                            v_isSharedCheck_4595_ = (!lean_is_exclusive(v___x_4582_)) as u8;
                            if v_isSharedCheck_4595_ == 0 {
                                v___x_4590_ = v___x_4582_;
                                v_isShared_4591_ = v_isSharedCheck_4595_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4588_);
                                lean_dec(v___x_4582_);
                                v___x_4590_ = lean_box(0);
                                v_isShared_4591_ = v_isSharedCheck_4595_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___y_4568_ = v___x_4581_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4565_);
                    v___y_4568_ = v___x_4577_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v_isShared_4591_ == 0 {
                    v___x_4593_ = v___x_4590_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
                    v___x_4593_ = v_reuseFailAlloc_4594_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4593_;
            }
            6 => {
                if v_isShared_4601_ == 0 {
                    v___x_4603_ = v___x_4600_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4598_);
                    v___x_4603_ = v_reuseFailAlloc_4604_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg___boxed(
    mut v_as_x27_4606_: *mut LeanObject,
    mut v_b_4607_: *mut LeanObject,
    mut v___y_4608_: *mut LeanObject,
    mut v___y_4609_: *mut LeanObject,
    mut v___y_4610_: *mut LeanObject,
    mut v___y_4611_: *mut LeanObject,
    mut v___y_4612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4613_: *mut LeanObject = core::ptr::null_mut();
    v_res_4613_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(
        v_as_x27_4606_,
        v_b_4607_,
        v___y_4608_,
        v___y_4609_,
        v___y_4610_,
        v___y_4611_,
    );
    lean_dec(v___y_4611_);
    lean_dec_ref(v___y_4610_);
    lean_dec(v___y_4609_);
    lean_dec_ref(v___y_4608_);
    lean_dec(v_as_x27_4606_);
    return v_res_4613_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(
    mut v_msgData_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
    mut v___y_4617_: *mut LeanObject,
    mut v___y_4618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    v___x_4620_ = lean_st_ref_get(v___y_4618_);
    v_env_4621_ = lean_ctor_get(v___x_4620_, 0);
    lean_inc_ref(v_env_4621_);
    lean_dec(v___x_4620_);
    v___x_4622_ = lean_st_ref_get(v___y_4616_);
    v_mctx_4623_ = lean_ctor_get(v___x_4622_, 0);
    lean_inc_ref(v_mctx_4623_);
    lean_dec(v___x_4622_);
    v_lctx_4624_ = lean_ctor_get(v___y_4615_, 2);
    v_options_4625_ = lean_ctor_get(v___y_4617_, 2);
    lean_inc_ref(v_options_4625_);
    lean_inc_ref(v_lctx_4624_);
    v___x_4626_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4626_, 0, v_env_4621_);
    lean_ctor_set(v___x_4626_, 1, v_mctx_4623_);
    lean_ctor_set(v___x_4626_, 2, v_lctx_4624_);
    lean_ctor_set(v___x_4626_, 3, v_options_4625_);
    v___x_4627_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4627_, 0, v___x_4626_);
    lean_ctor_set(v___x_4627_, 1, v_msgData_4614_);
    v___x_4628_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4628_, 0, v___x_4627_);
    return v___x_4628_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2___boxed(
    mut v_msgData_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
    mut v___y_4633_: *mut LeanObject,
    mut v___y_4634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4635_: *mut LeanObject = core::ptr::null_mut();
    v_res_4635_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msgData_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
    lean_dec(v___y_4633_);
    lean_dec_ref(v___y_4632_);
    lean_dec(v___y_4631_);
    lean_dec_ref(v___y_4630_);
    return v_res_4635_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(
    mut v_msg_4636_: *mut LeanObject,
    mut v___y_4637_: *mut LeanObject,
    mut v___y_4638_: *mut LeanObject,
    mut v___y_4639_: *mut LeanObject,
    mut v___y_4640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4647_: u8 = 0;
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4642_ = lean_ctor_get(v___y_4639_, 5);
                v___x_4643_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msg_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
                v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
                v_isSharedCheck_4652_ = (!lean_is_exclusive(v___x_4643_)) as u8;
                if v_isSharedCheck_4652_ == 0 {
                    v___x_4646_ = v___x_4643_;
                    v_isShared_4647_ = v_isSharedCheck_4652_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4644_);
                    lean_dec(v___x_4643_);
                    v___x_4646_ = lean_box(0);
                    v_isShared_4647_ = v_isSharedCheck_4652_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4642_);
                v___x_4648_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4648_, 0, v_ref_4642_);
                lean_ctor_set(v___x_4648_, 1, v_a_4644_);
                if v_isShared_4647_ == 0 {
                    lean_ctor_set_tag(v___x_4646_, 1);
                    lean_ctor_set(v___x_4646_, 0, v___x_4648_);
                    v___x_4650_ = v___x_4646_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4648_);
                    v___x_4650_ = v_reuseFailAlloc_4651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg___boxed(
    mut v_msg_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
    mut v___y_4657_: *mut LeanObject,
    mut v___y_4658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4659_: *mut LeanObject = core::ptr::null_mut();
    v_res_4659_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(
        v_msg_4653_,
        v___y_4654_,
        v___y_4655_,
        v___y_4656_,
        v___y_4657_,
    );
    lean_dec(v___y_4657_);
    lean_dec_ref(v___y_4656_);
    lean_dec(v___y_4655_);
    lean_dec_ref(v___y_4654_);
    return v_res_4659_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_convert___closed__1() -> *mut LeanObject {
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    v___x_4661_ = l_Lean_Elab_Tactic_Conv_convert___closed__0;
    v___x_4662_ = l_Lean_stringToMessageData(v___x_4661_);
    return v___x_4662_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_convert(
    mut v_lhs_4663_: *mut LeanObject,
    mut v_conv_4664_: *mut LeanObject,
    mut v_a_4665_: *mut LeanObject,
    mut v_a_4666_: *mut LeanObject,
    mut v_a_4667_: *mut LeanObject,
    mut v_a_4668_: *mut LeanObject,
    mut v_a_4669_: *mut LeanObject,
    mut v_a_4670_: *mut LeanObject,
    mut v_a_4671_: *mut LeanObject,
    mut v_a_4672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4689_: u8 = 0;
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4693_: u8 = 0;
    let mut v_unused_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4698_: u8 = 0;
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4702_: u8 = 0;
    let mut v___y_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4712_: u8 = 0;
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4719_: u8 = 0;
    let mut v_a_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4723_: u8 = 0;
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4727_: u8 = 0;
    let mut v_a_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: u8 = 0;
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4756_: u8 = 0;
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4760_: u8 = 0;
    let mut v_isSharedCheck_4761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4674_ = lean_box(0);
                v___x_4675_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(
                    v_lhs_4663_,
                    v___x_4674_,
                    v_a_4669_,
                    v_a_4670_,
                    v_a_4671_,
                    v_a_4672_,
                );
                if lean_obj_tag(v___x_4675_) == 0 {
                    v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
                    lean_inc(v_a_4676_);
                    lean_dec_ref_known(v___x_4675_, 1);
                    v_fst_4677_ = lean_ctor_get(v_a_4676_, 0);
                    v_snd_4678_ = lean_ctor_get(v_a_4676_, 1);
                    v_isSharedCheck_4761_ = (!lean_is_exclusive(v_a_4676_)) as u8;
                    if v_isSharedCheck_4761_ == 0 {
                        v___x_4680_ = v_a_4676_;
                        v_isShared_4681_ = v_isSharedCheck_4761_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4678_);
                        lean_inc(v_fst_4677_);
                        lean_dec(v_a_4676_);
                        v___x_4680_ = lean_box(0);
                        v_isShared_4681_ = v_isSharedCheck_4761_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_conv_4664_);
                    return v___x_4675_;
                }
            }
            1 => {
                v___x_4682_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_4666_);
                if lean_obj_tag(v___x_4682_) == 0 {
                    v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
                    lean_inc(v_a_4683_);
                    lean_dec_ref_known(v___x_4682_, 1);
                    v___x_4729_ = l_Lean_Expr_mvarId_x21(v_snd_4678_);
                    v___x_4730_ = lean_box(0);
                    v___x_4731_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4731_, 0, v___x_4729_);
                    lean_ctor_set(v___x_4731_, 1, v___x_4730_);
                    v___x_4732_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_4731_, v_a_4666_);
                    if lean_obj_tag(v___x_4732_) == 0 {
                        lean_dec_ref_known(v___x_4732_, 1);
                        lean_inc(v_a_4672_);
                        lean_inc_ref(v_a_4671_);
                        lean_inc(v_a_4670_);
                        lean_inc_ref(v_a_4669_);
                        lean_inc(v_a_4668_);
                        lean_inc_ref(v_a_4667_);
                        lean_inc(v_a_4666_);
                        lean_inc_ref(v_a_4665_);
                        v___x_4733_ = lean_apply_9(
                            v_conv_4664_,
                            v_a_4665_,
                            v_a_4666_,
                            v_a_4667_,
                            v_a_4668_,
                            v_a_4669_,
                            v_a_4670_,
                            v_a_4671_,
                            v_a_4672_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_4733_) == 0 {
                            lean_dec_ref_known(v___x_4733_, 1);
                            v___x_4734_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_4666_);
                            if lean_obj_tag(v___x_4734_) == 0 {
                                v_a_4735_ = lean_ctor_get(v___x_4734_, 0);
                                lean_inc(v_a_4735_);
                                lean_dec_ref_known(v___x_4734_, 1);
                                v___x_4736_ = lean_box(0);
                                v___x_4737_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(v_a_4735_, v___x_4736_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
                                lean_dec(v_a_4735_);
                                if lean_obj_tag(v___x_4737_) == 0 {
                                    lean_dec_ref_known(v___x_4737_, 1);
                                    v___x_4738_ = l_Lean_Elab_Tactic_pruneSolvedGoals(
                                        v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_,
                                        v_a_4670_, v_a_4671_, v_a_4672_,
                                    );
                                    if lean_obj_tag(v___x_4738_) == 0 {
                                        lean_dec_ref_known(v___x_4738_, 1);
                                        v___x_4739_ =
                                            l_Lean_Elab_Tactic_getGoals___redArg(v_a_4666_);
                                        if lean_obj_tag(v___x_4739_) == 0 {
                                            v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
                                            lean_inc(v_a_4740_);
                                            lean_dec_ref_known(v___x_4739_, 1);
                                            v___x_4741_ = l_List_isEmpty___redArg(v_a_4740_);
                                            lean_dec(v_a_4740_);
                                            if v___x_4741_ == 0 {
                                                v___x_4742_ =
                                                    l_Lean_Elab_Tactic_getGoals___redArg(v_a_4666_);
                                                if lean_obj_tag(v___x_4742_) == 0 {
                                                    v_a_4743_ = lean_ctor_get(v___x_4742_, 0);
                                                    lean_inc(v_a_4743_);
                                                    lean_dec_ref_known(v___x_4742_, 1);
                                                    v___x_4744_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_convert___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_convert___closed__1_once), _init_l_Lean_Elab_Tactic_Conv_convert___closed__1);
                                                    v___x_4745_ =
                                                        l_Lean_Elab_goalsToMessageData(v_a_4743_);
                                                    v___x_4746_ = lean_alloc_ctor(7, 2, (0) as u32);
                                                    lean_ctor_set(v___x_4746_, 0, v___x_4744_);
                                                    lean_ctor_set(v___x_4746_, 1, v___x_4745_);
                                                    v___x_4747_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(v___x_4746_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
                                                    v___y_4704_ = v___x_4747_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    lean_del_object(v___x_4680_);
                                                    lean_dec(v_snd_4678_);
                                                    lean_dec(v_fst_4677_);
                                                    v_a_4748_ = lean_ctor_get(v___x_4742_, 0);
                                                    lean_inc(v_a_4748_);
                                                    lean_dec_ref_known(v___x_4742_, 1);
                                                    v_a_4685_ = v_a_4748_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                v___x_4749_ =
                                                    l_Lean_Elab_Tactic_Conv_convert___lam__0(
                                                        v___x_4736_,
                                                        v_a_4665_,
                                                        v_a_4666_,
                                                        v_a_4667_,
                                                        v_a_4668_,
                                                        v_a_4669_,
                                                        v_a_4670_,
                                                        v_a_4671_,
                                                        v_a_4672_,
                                                    );
                                                v___y_4704_ = v___x_4749_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            lean_del_object(v___x_4680_);
                                            lean_dec(v_snd_4678_);
                                            lean_dec(v_fst_4677_);
                                            v_a_4750_ = lean_ctor_get(v___x_4739_, 0);
                                            lean_inc(v_a_4750_);
                                            lean_dec_ref_known(v___x_4739_, 1);
                                            v_a_4685_ = v_a_4750_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        v___y_4704_ = v___x_4738_;
                                        state = 7;
                                        continue;
                                    }
                                } else {
                                    v___y_4704_ = v___x_4737_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_4680_);
                                lean_dec(v_snd_4678_);
                                lean_dec(v_fst_4677_);
                                v_a_4751_ = lean_ctor_get(v___x_4734_, 0);
                                lean_inc(v_a_4751_);
                                lean_dec_ref_known(v___x_4734_, 1);
                                v_a_4685_ = v_a_4751_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4680_);
                            lean_dec(v_snd_4678_);
                            lean_dec(v_fst_4677_);
                            v_a_4752_ = lean_ctor_get(v___x_4733_, 0);
                            lean_inc(v_a_4752_);
                            lean_dec_ref_known(v___x_4733_, 1);
                            v_a_4685_ = v_a_4752_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_conv_4664_);
                        v___y_4704_ = v___x_4732_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4680_);
                    lean_dec(v_snd_4678_);
                    lean_dec(v_fst_4677_);
                    lean_dec_ref(v_conv_4664_);
                    v_a_4753_ = lean_ctor_get(v___x_4682_, 0);
                    v_isSharedCheck_4760_ = (!lean_is_exclusive(v___x_4682_)) as u8;
                    if v_isSharedCheck_4760_ == 0 {
                        v___x_4755_ = v___x_4682_;
                        v_isShared_4756_ = v_isSharedCheck_4760_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4753_);
                        lean_dec(v___x_4682_);
                        v___x_4755_ = lean_box(0);
                        v_isShared_4756_ = v_isSharedCheck_4760_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4686_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_4683_, v_a_4666_);
                if lean_obj_tag(v___x_4686_) == 0 {
                    v_isSharedCheck_4693_ = (!lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4693_ == 0 {
                        v_unused_4694_ = lean_ctor_get(v___x_4686_, 0);
                        lean_dec(v_unused_4694_);
                        v___x_4688_ = v___x_4686_;
                        v_isShared_4689_ = v_isSharedCheck_4693_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_4686_);
                        v___x_4688_ = lean_box(0);
                        v_isShared_4689_ = v_isSharedCheck_4693_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_4685_);
                    v_a_4695_ = lean_ctor_get(v___x_4686_, 0);
                    v_isSharedCheck_4702_ = (!lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4702_ == 0 {
                        v___x_4697_ = v___x_4686_;
                        v_isShared_4698_ = v_isSharedCheck_4702_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4695_);
                        lean_dec(v___x_4686_);
                        v___x_4697_ = lean_box(0);
                        v_isShared_4698_ = v_isSharedCheck_4702_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4689_ == 0 {
                    lean_ctor_set_tag(v___x_4688_, 1);
                    lean_ctor_set(v___x_4688_, 0, v_a_4685_);
                    v___x_4691_ = v___x_4688_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4685_);
                    v___x_4691_ = v_reuseFailAlloc_4692_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4691_;
            }
            5 => {
                if v_isShared_4698_ == 0 {
                    v___x_4700_ = v___x_4697_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4695_);
                    v___x_4700_ = v_reuseFailAlloc_4701_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4700_;
            }
            7 => {
                if lean_obj_tag(v___y_4704_) == 0 {
                    lean_dec_ref_known(v___y_4704_, 1);
                    v___x_4705_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_4683_, v_a_4666_);
                    if lean_obj_tag(v___x_4705_) == 0 {
                        lean_dec_ref_known(v___x_4705_, 1);
                        v___x_4706_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_fst_4677_, v_a_4670_);
                        v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
                        lean_inc(v_a_4707_);
                        lean_dec_ref(v___x_4706_);
                        v___x_4708_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_snd_4678_, v_a_4670_);
                        v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
                        v_isSharedCheck_4719_ = (!lean_is_exclusive(v___x_4708_)) as u8;
                        if v_isSharedCheck_4719_ == 0 {
                            v___x_4711_ = v___x_4708_;
                            v_isShared_4712_ = v_isSharedCheck_4719_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_4709_);
                            lean_dec(v___x_4708_);
                            v___x_4711_ = lean_box(0);
                            v_isShared_4712_ = v_isSharedCheck_4719_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4680_);
                        lean_dec(v_snd_4678_);
                        lean_dec(v_fst_4677_);
                        v_a_4720_ = lean_ctor_get(v___x_4705_, 0);
                        v_isSharedCheck_4727_ = (!lean_is_exclusive(v___x_4705_)) as u8;
                        if v_isSharedCheck_4727_ == 0 {
                            v___x_4722_ = v___x_4705_;
                            v_isShared_4723_ = v_isSharedCheck_4727_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_4720_);
                            lean_dec(v___x_4705_);
                            v___x_4722_ = lean_box(0);
                            v_isShared_4723_ = v_isSharedCheck_4727_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4680_);
                    lean_dec(v_snd_4678_);
                    lean_dec(v_fst_4677_);
                    v_a_4728_ = lean_ctor_get(v___y_4704_, 0);
                    lean_inc(v_a_4728_);
                    lean_dec_ref_known(v___y_4704_, 1);
                    v_a_4685_ = v_a_4728_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                if v_isShared_4681_ == 0 {
                    lean_ctor_set(v___x_4680_, 1, v_a_4709_);
                    lean_ctor_set(v___x_4680_, 0, v_a_4707_);
                    v___x_4714_ = v___x_4680_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4707_);
                    lean_ctor_set(v_reuseFailAlloc_4718_, 1, v_a_4709_);
                    v___x_4714_ = v_reuseFailAlloc_4718_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4712_ == 0 {
                    lean_ctor_set(v___x_4711_, 0, v___x_4714_);
                    v___x_4716_ = v___x_4711_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4714_);
                    v___x_4716_ = v_reuseFailAlloc_4717_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4716_;
            }
            11 => {
                if v_isShared_4723_ == 0 {
                    v___x_4725_ = v___x_4722_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
                    v___x_4725_ = v_reuseFailAlloc_4726_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4725_;
            }
            13 => {
                if v_isShared_4756_ == 0 {
                    v___x_4758_ = v___x_4755_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
                    v___x_4758_ = v_reuseFailAlloc_4759_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_convert___boxed(
    mut v_lhs_4762_: *mut LeanObject,
    mut v_conv_4763_: *mut LeanObject,
    mut v_a_4764_: *mut LeanObject,
    mut v_a_4765_: *mut LeanObject,
    mut v_a_4766_: *mut LeanObject,
    mut v_a_4767_: *mut LeanObject,
    mut v_a_4768_: *mut LeanObject,
    mut v_a_4769_: *mut LeanObject,
    mut v_a_4770_: *mut LeanObject,
    mut v_a_4771_: *mut LeanObject,
    mut v_a_4772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4773_: *mut LeanObject = core::ptr::null_mut();
    v_res_4773_ = l_Lean_Elab_Tactic_Conv_convert(
        v_lhs_4762_,
        v_conv_4763_,
        v_a_4764_,
        v_a_4765_,
        v_a_4766_,
        v_a_4767_,
        v_a_4768_,
        v_a_4769_,
        v_a_4770_,
        v_a_4771_,
    );
    lean_dec(v_a_4771_);
    lean_dec_ref(v_a_4770_);
    lean_dec(v_a_4769_);
    lean_dec_ref(v_a_4768_);
    lean_dec(v_a_4767_);
    lean_dec_ref(v_a_4766_);
    lean_dec(v_a_4765_);
    lean_dec_ref(v_a_4764_);
    return v_res_4773_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1(
    mut v_as_4774_: *mut LeanObject,
    mut v_as_x27_4775_: *mut LeanObject,
    mut v_b_4776_: *mut LeanObject,
    mut v_a_4777_: *mut LeanObject,
    mut v___y_4778_: *mut LeanObject,
    mut v___y_4779_: *mut LeanObject,
    mut v___y_4780_: *mut LeanObject,
    mut v___y_4781_: *mut LeanObject,
    mut v___y_4782_: *mut LeanObject,
    mut v___y_4783_: *mut LeanObject,
    mut v___y_4784_: *mut LeanObject,
    mut v___y_4785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    v___x_4787_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(
        v_as_x27_4775_,
        v_b_4776_,
        v___y_4782_,
        v___y_4783_,
        v___y_4784_,
        v___y_4785_,
    );
    return v___x_4787_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___boxed(
    mut v_as_4788_: *mut LeanObject,
    mut v_as_x27_4789_: *mut LeanObject,
    mut v_b_4790_: *mut LeanObject,
    mut v_a_4791_: *mut LeanObject,
    mut v___y_4792_: *mut LeanObject,
    mut v___y_4793_: *mut LeanObject,
    mut v___y_4794_: *mut LeanObject,
    mut v___y_4795_: *mut LeanObject,
    mut v___y_4796_: *mut LeanObject,
    mut v___y_4797_: *mut LeanObject,
    mut v___y_4798_: *mut LeanObject,
    mut v___y_4799_: *mut LeanObject,
    mut v___y_4800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4801_: *mut LeanObject = core::ptr::null_mut();
    v_res_4801_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1(
        v_as_4788_,
        v_as_x27_4789_,
        v_b_4790_,
        v_a_4791_,
        v___y_4792_,
        v___y_4793_,
        v___y_4794_,
        v___y_4795_,
        v___y_4796_,
        v___y_4797_,
        v___y_4798_,
        v___y_4799_,
    );
    lean_dec(v___y_4799_);
    lean_dec_ref(v___y_4798_);
    lean_dec(v___y_4797_);
    lean_dec_ref(v___y_4796_);
    lean_dec(v___y_4795_);
    lean_dec_ref(v___y_4794_);
    lean_dec(v___y_4793_);
    lean_dec_ref(v___y_4792_);
    lean_dec(v_as_x27_4789_);
    lean_dec(v_as_4788_);
    return v_res_4801_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2(
    mut v_00_u03b1_4802_: *mut LeanObject,
    mut v_msg_4803_: *mut LeanObject,
    mut v___y_4804_: *mut LeanObject,
    mut v___y_4805_: *mut LeanObject,
    mut v___y_4806_: *mut LeanObject,
    mut v___y_4807_: *mut LeanObject,
    mut v___y_4808_: *mut LeanObject,
    mut v___y_4809_: *mut LeanObject,
    mut v___y_4810_: *mut LeanObject,
    mut v___y_4811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    v___x_4813_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(
        v_msg_4803_,
        v___y_4808_,
        v___y_4809_,
        v___y_4810_,
        v___y_4811_,
    );
    return v___x_4813_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___boxed(
    mut v_00_u03b1_4814_: *mut LeanObject,
    mut v_msg_4815_: *mut LeanObject,
    mut v___y_4816_: *mut LeanObject,
    mut v___y_4817_: *mut LeanObject,
    mut v___y_4818_: *mut LeanObject,
    mut v___y_4819_: *mut LeanObject,
    mut v___y_4820_: *mut LeanObject,
    mut v___y_4821_: *mut LeanObject,
    mut v___y_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
    mut v___y_4824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4825_: *mut LeanObject = core::ptr::null_mut();
    v_res_4825_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2(
        v_00_u03b1_4814_,
        v_msg_4815_,
        v___y_4816_,
        v___y_4817_,
        v___y_4818_,
        v___y_4819_,
        v___y_4820_,
        v___y_4821_,
        v___y_4822_,
        v___y_4823_,
    );
    lean_dec(v___y_4823_);
    lean_dec_ref(v___y_4822_);
    lean_dec(v___y_4821_);
    lean_dec_ref(v___y_4820_);
    lean_dec(v___y_4819_);
    lean_dec_ref(v___y_4818_);
    lean_dec(v___y_4817_);
    lean_dec_ref(v___y_4816_);
    return v_res_4825_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(
    mut v_mvarId_4826_: *mut LeanObject,
    mut v_x_4827_: *mut LeanObject,
    mut v___y_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
    mut v___y_4831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4841_: u8 = 0;
    let mut v_a_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4845_: u8 = 0;
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4833_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_4826_,
                    v_x_4827_,
                    v___y_4828_,
                    v___y_4829_,
                    v___y_4830_,
                    v___y_4831_,
                );
                if lean_obj_tag(v___x_4833_) == 0 {
                    v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
                    v_isSharedCheck_4841_ = (!lean_is_exclusive(v___x_4833_)) as u8;
                    if v_isSharedCheck_4841_ == 0 {
                        v___x_4836_ = v___x_4833_;
                        v_isShared_4837_ = v_isSharedCheck_4841_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4834_);
                        lean_dec(v___x_4833_);
                        v___x_4836_ = lean_box(0);
                        v_isShared_4837_ = v_isSharedCheck_4841_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4842_ = lean_ctor_get(v___x_4833_, 0);
                    v_isSharedCheck_4849_ = (!lean_is_exclusive(v___x_4833_)) as u8;
                    if v_isSharedCheck_4849_ == 0 {
                        v___x_4844_ = v___x_4833_;
                        v_isShared_4845_ = v_isSharedCheck_4849_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4842_);
                        lean_dec(v___x_4833_);
                        v___x_4844_ = lean_box(0);
                        v_isShared_4845_ = v_isSharedCheck_4849_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4837_ == 0 {
                    v___x_4839_ = v___x_4836_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4840_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
                    v___x_4839_ = v_reuseFailAlloc_4840_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4839_;
            }
            3 => {
                if v_isShared_4845_ == 0 {
                    v___x_4847_ = v___x_4844_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
                    v___x_4847_ = v_reuseFailAlloc_4848_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg___boxed(
    mut v_mvarId_4850_: *mut LeanObject,
    mut v_x_4851_: *mut LeanObject,
    mut v___y_4852_: *mut LeanObject,
    mut v___y_4853_: *mut LeanObject,
    mut v___y_4854_: *mut LeanObject,
    mut v___y_4855_: *mut LeanObject,
    mut v___y_4856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4857_: *mut LeanObject = core::ptr::null_mut();
    v_res_4857_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(
            v_mvarId_4850_,
            v_x_4851_,
            v___y_4852_,
            v___y_4853_,
            v___y_4854_,
            v___y_4855_,
        );
    lean_dec(v___y_4855_);
    lean_dec_ref(v___y_4854_);
    lean_dec(v___y_4853_);
    lean_dec_ref(v___y_4852_);
    return v_res_4857_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1(
    mut v_00_u03b1_4858_: *mut LeanObject,
    mut v_mvarId_4859_: *mut LeanObject,
    mut v_x_4860_: *mut LeanObject,
    mut v___y_4861_: *mut LeanObject,
    mut v___y_4862_: *mut LeanObject,
    mut v___y_4863_: *mut LeanObject,
    mut v___y_4864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    v___x_4866_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(
            v_mvarId_4859_,
            v_x_4860_,
            v___y_4861_,
            v___y_4862_,
            v___y_4863_,
            v___y_4864_,
        );
    return v___x_4866_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___boxed(
    mut v_00_u03b1_4867_: *mut LeanObject,
    mut v_mvarId_4868_: *mut LeanObject,
    mut v_x_4869_: *mut LeanObject,
    mut v___y_4870_: *mut LeanObject,
    mut v___y_4871_: *mut LeanObject,
    mut v___y_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4875_: *mut LeanObject = core::ptr::null_mut();
    v_res_4875_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1(
        v_00_u03b1_4867_,
        v_mvarId_4868_,
        v_x_4869_,
        v___y_4870_,
        v___y_4871_,
        v___y_4872_,
        v___y_4873_,
    );
    lean_dec(v___y_4873_);
    lean_dec_ref(v___y_4872_);
    lean_dec(v___y_4871_);
    lean_dec_ref(v___y_4870_);
    return v_res_4875_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(
    mut v_msg_4876_: *mut LeanObject,
    mut v___y_4877_: *mut LeanObject,
    mut v___y_4878_: *mut LeanObject,
    mut v___y_4879_: *mut LeanObject,
    mut v___y_4880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4887_: u8 = 0;
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4882_ = lean_ctor_get(v___y_4879_, 5);
                v___x_4883_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msg_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
                v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
                v_isSharedCheck_4892_ = (!lean_is_exclusive(v___x_4883_)) as u8;
                if v_isSharedCheck_4892_ == 0 {
                    v___x_4886_ = v___x_4883_;
                    v_isShared_4887_ = v_isSharedCheck_4892_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4884_);
                    lean_dec(v___x_4883_);
                    v___x_4886_ = lean_box(0);
                    v_isShared_4887_ = v_isSharedCheck_4892_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4882_);
                v___x_4888_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4888_, 0, v_ref_4882_);
                lean_ctor_set(v___x_4888_, 1, v_a_4884_);
                if v_isShared_4887_ == 0 {
                    lean_ctor_set_tag(v___x_4886_, 1);
                    lean_ctor_set(v___x_4886_, 0, v___x_4888_);
                    v___x_4890_ = v___x_4886_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4888_);
                    v___x_4890_ = v_reuseFailAlloc_4891_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg___boxed(
    mut v_msg_4893_: *mut LeanObject,
    mut v___y_4894_: *mut LeanObject,
    mut v___y_4895_: *mut LeanObject,
    mut v___y_4896_: *mut LeanObject,
    mut v___y_4897_: *mut LeanObject,
    mut v___y_4898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4899_: *mut LeanObject = core::ptr::null_mut();
    v_res_4899_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(
        v_msg_4893_,
        v___y_4894_,
        v___y_4895_,
        v___y_4896_,
        v___y_4897_,
    );
    lean_dec(v___y_4897_);
    lean_dec_ref(v___y_4896_);
    lean_dec(v___y_4895_);
    lean_dec_ref(v___y_4894_);
    return v_res_4899_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1() -> *mut LeanObject
{
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    v___x_4901_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0;
    v___x_4902_ = l_Lean_stringToMessageData(v___x_4901_);
    return v___x_4902_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0(
    mut v_mvarId_4903_: *mut LeanObject,
    mut v___y_4904_: *mut LeanObject,
    mut v___y_4905_: *mut LeanObject,
    mut v___y_4906_: *mut LeanObject,
    mut v___y_4907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4915_: u8 = 0;
    let mut v_val_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v_a_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4931_: u8 = 0;
    let mut v_a_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4935_: u8 = 0;
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4939_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4909_ = l_Lean_MVarId_getType(
                    v_mvarId_4903_,
                    v___y_4904_,
                    v___y_4905_,
                    v___y_4906_,
                    v___y_4907_,
                );
                if lean_obj_tag(v___x_4909_) == 0 {
                    v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
                    lean_inc(v_a_4910_);
                    lean_dec_ref_known(v___x_4909_, 1);
                    v___x_4911_ = l_Lean_Meta_matchEq_x3f(
                        v_a_4910_,
                        v___y_4904_,
                        v___y_4905_,
                        v___y_4906_,
                        v___y_4907_,
                    );
                    if lean_obj_tag(v___x_4911_) == 0 {
                        v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
                        v_isSharedCheck_4923_ = (!lean_is_exclusive(v___x_4911_)) as u8;
                        if v_isSharedCheck_4923_ == 0 {
                            v___x_4914_ = v___x_4911_;
                            v_isShared_4915_ = v_isSharedCheck_4923_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4912_);
                            lean_dec(v___x_4911_);
                            v___x_4914_ = lean_box(0);
                            v_isShared_4915_ = v_isSharedCheck_4923_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4924_ = lean_ctor_get(v___x_4911_, 0);
                        v_isSharedCheck_4931_ = (!lean_is_exclusive(v___x_4911_)) as u8;
                        if v_isSharedCheck_4931_ == 0 {
                            v___x_4926_ = v___x_4911_;
                            v_isShared_4927_ = v_isSharedCheck_4931_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4924_);
                            lean_dec(v___x_4911_);
                            v___x_4926_ = lean_box(0);
                            v_isShared_4927_ = v_isSharedCheck_4931_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4932_ = lean_ctor_get(v___x_4909_, 0);
                    v_isSharedCheck_4939_ = (!lean_is_exclusive(v___x_4909_)) as u8;
                    if v_isSharedCheck_4939_ == 0 {
                        v___x_4934_ = v___x_4909_;
                        v_isShared_4935_ = v_isSharedCheck_4939_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4932_);
                        lean_dec(v___x_4909_);
                        v___x_4934_ = lean_box(0);
                        v_isShared_4935_ = v_isSharedCheck_4939_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4912_) == 1 {
                    v_val_4916_ = lean_ctor_get(v_a_4912_, 0);
                    lean_inc(v_val_4916_);
                    lean_dec_ref_known(v_a_4912_, 1);
                    v_snd_4917_ = lean_ctor_get(v_val_4916_, 1);
                    lean_inc(v_snd_4917_);
                    lean_dec(v_val_4916_);
                    if v_isShared_4915_ == 0 {
                        lean_ctor_set(v___x_4914_, 0, v_snd_4917_);
                        v___x_4919_ = v___x_4914_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_snd_4917_);
                        v___x_4919_ = v_reuseFailAlloc_4920_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4914_);
                    lean_dec(v_a_4912_);
                    v___x_4921_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1,
                    );
                    v___x_4922_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(v___x_4921_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
                    return v___x_4922_;
                }
            }
            2 => {
                return v___x_4919_;
            }
            3 => {
                if v_isShared_4927_ == 0 {
                    v___x_4929_ = v___x_4926_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
                    v___x_4929_ = v_reuseFailAlloc_4930_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4929_;
            }
            5 => {
                if v_isShared_4935_ == 0 {
                    v___x_4937_ = v___x_4934_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
                    v___x_4937_ = v_reuseFailAlloc_4938_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4937_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___boxed(
    mut v_mvarId_4940_: *mut LeanObject,
    mut v___y_4941_: *mut LeanObject,
    mut v___y_4942_: *mut LeanObject,
    mut v___y_4943_: *mut LeanObject,
    mut v___y_4944_: *mut LeanObject,
    mut v___y_4945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4946_: *mut LeanObject = core::ptr::null_mut();
    v_res_4946_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0(
        v_mvarId_4940_,
        v___y_4941_,
        v___y_4942_,
        v___y_4943_,
        v___y_4944_,
    );
    lean_dec(v___y_4944_);
    lean_dec_ref(v___y_4943_);
    lean_dec(v___y_4942_);
    lean_dec_ref(v___y_4941_);
    return v_res_4946_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhsRhsCore(
    mut v_mvarId_4947_: *mut LeanObject,
    mut v_a_4948_: *mut LeanObject,
    mut v_a_4949_: *mut LeanObject,
    mut v_a_4950_: *mut LeanObject,
    mut v_a_4951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_4947_);
    v___f_4953_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_4953_, 0, v_mvarId_4947_);
    v___x_4954_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(
            v_mvarId_4947_,
            v___f_4953_,
            v_a_4948_,
            v_a_4949_,
            v_a_4950_,
            v_a_4951_,
        );
    return v___x_4954_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhsRhsCore___boxed(
    mut v_mvarId_4955_: *mut LeanObject,
    mut v_a_4956_: *mut LeanObject,
    mut v_a_4957_: *mut LeanObject,
    mut v_a_4958_: *mut LeanObject,
    mut v_a_4959_: *mut LeanObject,
    mut v_a_4960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4961_: *mut LeanObject = core::ptr::null_mut();
    v_res_4961_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(
        v_mvarId_4955_,
        v_a_4956_,
        v_a_4957_,
        v_a_4958_,
        v_a_4959_,
    );
    lean_dec(v_a_4959_);
    lean_dec_ref(v_a_4958_);
    lean_dec(v_a_4957_);
    lean_dec_ref(v_a_4956_);
    return v_res_4961_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0(
    mut v_00_u03b1_4962_: *mut LeanObject,
    mut v_msg_4963_: *mut LeanObject,
    mut v___y_4964_: *mut LeanObject,
    mut v___y_4965_: *mut LeanObject,
    mut v___y_4966_: *mut LeanObject,
    mut v___y_4967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    v___x_4969_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(
        v_msg_4963_,
        v___y_4964_,
        v___y_4965_,
        v___y_4966_,
        v___y_4967_,
    );
    return v___x_4969_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___boxed(
    mut v_00_u03b1_4970_: *mut LeanObject,
    mut v_msg_4971_: *mut LeanObject,
    mut v___y_4972_: *mut LeanObject,
    mut v___y_4973_: *mut LeanObject,
    mut v___y_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4977_: *mut LeanObject = core::ptr::null_mut();
    v_res_4977_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0(
        v_00_u03b1_4970_,
        v_msg_4971_,
        v___y_4972_,
        v___y_4973_,
        v___y_4974_,
        v___y_4975_,
    );
    lean_dec(v___y_4975_);
    lean_dec_ref(v___y_4974_);
    lean_dec(v___y_4973_);
    lean_dec_ref(v___y_4972_);
    return v_res_4977_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(
    mut v_a_4978_: *mut LeanObject,
    mut v_a_4979_: *mut LeanObject,
    mut v_a_4980_: *mut LeanObject,
    mut v_a_4981_: *mut LeanObject,
    mut v_a_4982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4990_: u8 = 0;
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4984_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_,
                );
                if lean_obj_tag(v___x_4984_) == 0 {
                    v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
                    lean_inc(v_a_4985_);
                    lean_dec_ref_known(v___x_4984_, 1);
                    v___x_4986_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(
                        v_a_4985_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_,
                    );
                    return v___x_4986_;
                } else {
                    v_a_4987_ = lean_ctor_get(v___x_4984_, 0);
                    v_isSharedCheck_4994_ = (!lean_is_exclusive(v___x_4984_)) as u8;
                    if v_isSharedCheck_4994_ == 0 {
                        v___x_4989_ = v___x_4984_;
                        v_isShared_4990_ = v_isSharedCheck_4994_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4987_);
                        lean_dec(v___x_4984_);
                        v___x_4989_ = lean_box(0);
                        v_isShared_4990_ = v_isSharedCheck_4994_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4990_ == 0 {
                    v___x_4992_ = v___x_4989_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4993_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
                    v___x_4992_ = v_reuseFailAlloc_4993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg___boxed(
    mut v_a_4995_: *mut LeanObject,
    mut v_a_4996_: *mut LeanObject,
    mut v_a_4997_: *mut LeanObject,
    mut v_a_4998_: *mut LeanObject,
    mut v_a_4999_: *mut LeanObject,
    mut v_a_5000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5001_: *mut LeanObject = core::ptr::null_mut();
    v_res_5001_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(
        v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_,
    );
    lean_dec(v_a_4999_);
    lean_dec_ref(v_a_4998_);
    lean_dec(v_a_4997_);
    lean_dec_ref(v_a_4996_);
    lean_dec(v_a_4995_);
    return v_res_5001_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhsRhs(
    mut v_a_5002_: *mut LeanObject,
    mut v_a_5003_: *mut LeanObject,
    mut v_a_5004_: *mut LeanObject,
    mut v_a_5005_: *mut LeanObject,
    mut v_a_5006_: *mut LeanObject,
    mut v_a_5007_: *mut LeanObject,
    mut v_a_5008_: *mut LeanObject,
    mut v_a_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    v___x_5011_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(
        v_a_5003_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_,
    );
    return v___x_5011_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhsRhs___boxed(
    mut v_a_5012_: *mut LeanObject,
    mut v_a_5013_: *mut LeanObject,
    mut v_a_5014_: *mut LeanObject,
    mut v_a_5015_: *mut LeanObject,
    mut v_a_5016_: *mut LeanObject,
    mut v_a_5017_: *mut LeanObject,
    mut v_a_5018_: *mut LeanObject,
    mut v_a_5019_: *mut LeanObject,
    mut v_a_5020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5021_: *mut LeanObject = core::ptr::null_mut();
    v_res_5021_ = l_Lean_Elab_Tactic_Conv_getLhsRhs(
        v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_,
    );
    lean_dec(v_a_5019_);
    lean_dec_ref(v_a_5018_);
    lean_dec(v_a_5017_);
    lean_dec_ref(v_a_5016_);
    lean_dec(v_a_5015_);
    lean_dec_ref(v_a_5014_);
    lean_dec(v_a_5013_);
    lean_dec_ref(v_a_5012_);
    return v_res_5021_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhs___redArg(
    mut v_a_5022_: *mut LeanObject,
    mut v_a_5023_: *mut LeanObject,
    mut v_a_5024_: *mut LeanObject,
    mut v_a_5025_: *mut LeanObject,
    mut v_a_5026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5032_: u8 = 0;
    let mut v_fst_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5037_: u8 = 0;
    let mut v_a_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5041_: u8 = 0;
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5028_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(
                    v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_,
                );
                if lean_obj_tag(v___x_5028_) == 0 {
                    v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
                    v_isSharedCheck_5037_ = (!lean_is_exclusive(v___x_5028_)) as u8;
                    if v_isSharedCheck_5037_ == 0 {
                        v___x_5031_ = v___x_5028_;
                        v_isShared_5032_ = v_isSharedCheck_5037_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5029_);
                        lean_dec(v___x_5028_);
                        v___x_5031_ = lean_box(0);
                        v_isShared_5032_ = v_isSharedCheck_5037_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5038_ = lean_ctor_get(v___x_5028_, 0);
                    v_isSharedCheck_5045_ = (!lean_is_exclusive(v___x_5028_)) as u8;
                    if v_isSharedCheck_5045_ == 0 {
                        v___x_5040_ = v___x_5028_;
                        v_isShared_5041_ = v_isSharedCheck_5045_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5038_);
                        lean_dec(v___x_5028_);
                        v___x_5040_ = lean_box(0);
                        v_isShared_5041_ = v_isSharedCheck_5045_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5033_ = lean_ctor_get(v_a_5029_, 0);
                lean_inc(v_fst_5033_);
                lean_dec(v_a_5029_);
                if v_isShared_5032_ == 0 {
                    lean_ctor_set(v___x_5031_, 0, v_fst_5033_);
                    v___x_5035_ = v___x_5031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_fst_5033_);
                    v___x_5035_ = v_reuseFailAlloc_5036_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5035_;
            }
            3 => {
                if v_isShared_5041_ == 0 {
                    v___x_5043_ = v___x_5040_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_a_5038_);
                    v___x_5043_ = v_reuseFailAlloc_5044_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhs___redArg___boxed(
    mut v_a_5046_: *mut LeanObject,
    mut v_a_5047_: *mut LeanObject,
    mut v_a_5048_: *mut LeanObject,
    mut v_a_5049_: *mut LeanObject,
    mut v_a_5050_: *mut LeanObject,
    mut v_a_5051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5052_: *mut LeanObject = core::ptr::null_mut();
    v_res_5052_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
        v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_,
    );
    lean_dec(v_a_5050_);
    lean_dec_ref(v_a_5049_);
    lean_dec(v_a_5048_);
    lean_dec_ref(v_a_5047_);
    lean_dec(v_a_5046_);
    return v_res_5052_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhs(
    mut v_a_5053_: *mut LeanObject,
    mut v_a_5054_: *mut LeanObject,
    mut v_a_5055_: *mut LeanObject,
    mut v_a_5056_: *mut LeanObject,
    mut v_a_5057_: *mut LeanObject,
    mut v_a_5058_: *mut LeanObject,
    mut v_a_5059_: *mut LeanObject,
    mut v_a_5060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    v___x_5062_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
        v_a_5054_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_,
    );
    return v___x_5062_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getLhs___boxed(
    mut v_a_5063_: *mut LeanObject,
    mut v_a_5064_: *mut LeanObject,
    mut v_a_5065_: *mut LeanObject,
    mut v_a_5066_: *mut LeanObject,
    mut v_a_5067_: *mut LeanObject,
    mut v_a_5068_: *mut LeanObject,
    mut v_a_5069_: *mut LeanObject,
    mut v_a_5070_: *mut LeanObject,
    mut v_a_5071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5072_: *mut LeanObject = core::ptr::null_mut();
    v_res_5072_ = l_Lean_Elab_Tactic_Conv_getLhs(
        v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_,
    );
    lean_dec(v_a_5070_);
    lean_dec_ref(v_a_5069_);
    lean_dec(v_a_5068_);
    lean_dec_ref(v_a_5067_);
    lean_dec(v_a_5066_);
    lean_dec_ref(v_a_5065_);
    lean_dec(v_a_5064_);
    lean_dec_ref(v_a_5063_);
    return v_res_5072_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getRhs___redArg(
    mut v_a_5073_: *mut LeanObject,
    mut v_a_5074_: *mut LeanObject,
    mut v_a_5075_: *mut LeanObject,
    mut v_a_5076_: *mut LeanObject,
    mut v_a_5077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v_snd_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5088_: u8 = 0;
    let mut v_a_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5092_: u8 = 0;
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5079_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(
                    v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_,
                );
                if lean_obj_tag(v___x_5079_) == 0 {
                    v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
                    v_isSharedCheck_5088_ = (!lean_is_exclusive(v___x_5079_)) as u8;
                    if v_isSharedCheck_5088_ == 0 {
                        v___x_5082_ = v___x_5079_;
                        v_isShared_5083_ = v_isSharedCheck_5088_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5080_);
                        lean_dec(v___x_5079_);
                        v___x_5082_ = lean_box(0);
                        v_isShared_5083_ = v_isSharedCheck_5088_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5089_ = lean_ctor_get(v___x_5079_, 0);
                    v_isSharedCheck_5096_ = (!lean_is_exclusive(v___x_5079_)) as u8;
                    if v_isSharedCheck_5096_ == 0 {
                        v___x_5091_ = v___x_5079_;
                        v_isShared_5092_ = v_isSharedCheck_5096_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5089_);
                        lean_dec(v___x_5079_);
                        v___x_5091_ = lean_box(0);
                        v_isShared_5092_ = v_isSharedCheck_5096_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5084_ = lean_ctor_get(v_a_5080_, 1);
                lean_inc(v_snd_5084_);
                lean_dec(v_a_5080_);
                if v_isShared_5083_ == 0 {
                    lean_ctor_set(v___x_5082_, 0, v_snd_5084_);
                    v___x_5086_ = v___x_5082_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_snd_5084_);
                    v___x_5086_ = v_reuseFailAlloc_5087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5086_;
            }
            3 => {
                if v_isShared_5092_ == 0 {
                    v___x_5094_ = v___x_5091_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5095_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5089_);
                    v___x_5094_ = v_reuseFailAlloc_5095_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getRhs___redArg___boxed(
    mut v_a_5097_: *mut LeanObject,
    mut v_a_5098_: *mut LeanObject,
    mut v_a_5099_: *mut LeanObject,
    mut v_a_5100_: *mut LeanObject,
    mut v_a_5101_: *mut LeanObject,
    mut v_a_5102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5103_: *mut LeanObject = core::ptr::null_mut();
    v_res_5103_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(
        v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_,
    );
    lean_dec(v_a_5101_);
    lean_dec_ref(v_a_5100_);
    lean_dec(v_a_5099_);
    lean_dec_ref(v_a_5098_);
    lean_dec(v_a_5097_);
    return v_res_5103_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getRhs(
    mut v_a_5104_: *mut LeanObject,
    mut v_a_5105_: *mut LeanObject,
    mut v_a_5106_: *mut LeanObject,
    mut v_a_5107_: *mut LeanObject,
    mut v_a_5108_: *mut LeanObject,
    mut v_a_5109_: *mut LeanObject,
    mut v_a_5110_: *mut LeanObject,
    mut v_a_5111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    v___x_5113_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(
        v_a_5105_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_,
    );
    return v___x_5113_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_getRhs___boxed(
    mut v_a_5114_: *mut LeanObject,
    mut v_a_5115_: *mut LeanObject,
    mut v_a_5116_: *mut LeanObject,
    mut v_a_5117_: *mut LeanObject,
    mut v_a_5118_: *mut LeanObject,
    mut v_a_5119_: *mut LeanObject,
    mut v_a_5120_: *mut LeanObject,
    mut v_a_5121_: *mut LeanObject,
    mut v_a_5122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5123_: *mut LeanObject = core::ptr::null_mut();
    v_res_5123_ = l_Lean_Elab_Tactic_Conv_getRhs(
        v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_,
    );
    lean_dec(v_a_5121_);
    lean_dec_ref(v_a_5120_);
    lean_dec(v_a_5119_);
    lean_dec_ref(v_a_5118_);
    lean_dec(v_a_5117_);
    lean_dec_ref(v_a_5116_);
    lean_dec(v_a_5115_);
    lean_dec_ref(v_a_5114_);
    return v_res_5123_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_5124_: *mut LeanObject,
    mut v_x_5125_: *mut LeanObject,
    mut v_x_5126_: *mut LeanObject,
    mut v_x_5127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5132_: u8 = 0;
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: u8 = 0;
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5128_ = lean_ctor_get(v_x_5124_, 0);
                v_vs_5129_ = lean_ctor_get(v_x_5124_, 1);
                v_isSharedCheck_5153_ = (!lean_is_exclusive(v_x_5124_)) as u8;
                if v_isSharedCheck_5153_ == 0 {
                    v___x_5131_ = v_x_5124_;
                    v_isShared_5132_ = v_isSharedCheck_5153_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_5129_);
                    lean_inc(v_ks_5128_);
                    lean_dec(v_x_5124_);
                    v___x_5131_ = lean_box(0);
                    v_isShared_5132_ = v_isSharedCheck_5153_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5133_ = lean_array_get_size(v_ks_5128_);
                v___x_5134_ = lean_nat_dec_lt(v_x_5125_, v___x_5133_);
                if v___x_5134_ == 0 {
                    lean_dec(v_x_5125_);
                    v___x_5135_ = lean_array_push(v_ks_5128_, v_x_5126_);
                    v___x_5136_ = lean_array_push(v_vs_5129_, v_x_5127_);
                    if v_isShared_5132_ == 0 {
                        lean_ctor_set(v___x_5131_, 1, v___x_5136_);
                        lean_ctor_set(v___x_5131_, 0, v___x_5135_);
                        v___x_5138_ = v___x_5131_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5135_);
                        lean_ctor_set(v_reuseFailAlloc_5139_, 1, v___x_5136_);
                        v___x_5138_ = v_reuseFailAlloc_5139_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5140_ = lean_array_fget_borrowed(v_ks_5128_, v_x_5125_);
                    v___x_5141_ = l_Lean_instBEqMVarId_beq(v_x_5126_, v_k_x27_5140_);
                    if v___x_5141_ == 0 {
                        if v_isShared_5132_ == 0 {
                            v___x_5143_ = v___x_5131_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5147_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_ks_5128_);
                            lean_ctor_set(v_reuseFailAlloc_5147_, 1, v_vs_5129_);
                            v___x_5143_ = v_reuseFailAlloc_5147_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5148_ = lean_array_fset(v_ks_5128_, v_x_5125_, v_x_5126_);
                        v___x_5149_ = lean_array_fset(v_vs_5129_, v_x_5125_, v_x_5127_);
                        lean_dec(v_x_5125_);
                        if v_isShared_5132_ == 0 {
                            lean_ctor_set(v___x_5131_, 1, v___x_5149_);
                            lean_ctor_set(v___x_5131_, 0, v___x_5148_);
                            v___x_5151_ = v___x_5131_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5148_);
                            lean_ctor_set(v_reuseFailAlloc_5152_, 1, v___x_5149_);
                            v___x_5151_ = v_reuseFailAlloc_5152_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5138_;
            }
            3 => {
                v___x_5144_ = lean_unsigned_to_nat(1);
                v___x_5145_ = lean_nat_add(v_x_5125_, v___x_5144_);
                lean_dec(v_x_5125_);
                v_x_5124_ = v___x_5143_;
                v_x_5125_ = v___x_5145_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_5154_: *mut LeanObject,
    mut v_k_5155_: *mut LeanObject,
    mut v_v_5156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    v___x_5157_ = lean_unsigned_to_nat(0);
    v___x_5158_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_5154_, v___x_5157_, v_k_5155_, v_v_5156_);
    return v___x_5158_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_5159_: usize = 0;
    let mut v___x_5160_: usize = 0;
    let mut v___x_5161_: usize = 0;
    v___x_5159_ = 5usize;
    v___x_5160_ = 1usize;
    v___x_5161_ = lean_usize_shift_left(v___x_5160_, v___x_5159_);
    return v___x_5161_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_5162_: usize = 0;
    let mut v___x_5163_: usize = 0;
    let mut v___x_5164_: usize = 0;
    v___x_5162_ = 1usize;
    v___x_5163_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_5164_ = lean_usize_sub(v___x_5163_, v___x_5162_);
    return v___x_5164_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    v___x_5165_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_5165_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(
    mut v_x_5166_: *mut LeanObject,
    mut v_x_5167_: usize,
    mut v_x_5168_: usize,
    mut v_x_5169_: *mut LeanObject,
    mut v_x_5170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: usize = 0;
    let mut v___x_5173_: usize = 0;
    let mut v___x_5174_: usize = 0;
    let mut v___x_5175_: usize = 0;
    let mut v_j_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: u8 = 0;
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5181_: u8 = 0;
    let mut v_v_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5195_: u8 = 0;
    let mut v___x_5196_: u8 = 0;
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5202_: u8 = 0;
    let mut v_node_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5206_: u8 = 0;
    let mut v___x_5207_: usize = 0;
    let mut v___x_5208_: usize = 0;
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5213_: u8 = 0;
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5215_: u8 = 0;
    let mut v_unused_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5221_: u8 = 0;
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5226_: u8 = 0;
    let mut v_ks_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: usize = 0;
    let mut v___x_5233_: u8 = 0;
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: u8 = 0;
    let mut v_reuseFailAlloc_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5166_) == 0 {
                    v_es_5171_ = lean_ctor_get(v_x_5166_, 0);
                    v___x_5172_ = 5usize;
                    v___x_5173_ = 1usize;
                    v___x_5174_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_5175_ = lean_usize_land(v_x_5167_, v___x_5174_);
                    v_j_5176_ = lean_usize_to_nat(v___x_5175_);
                    v___x_5177_ = lean_array_get_size(v_es_5171_);
                    v___x_5178_ = lean_nat_dec_lt(v_j_5176_, v___x_5177_);
                    if v___x_5178_ == 0 {
                        lean_dec(v_j_5176_);
                        lean_dec(v_x_5170_);
                        lean_dec(v_x_5169_);
                        return v_x_5166_;
                    } else {
                        lean_inc_ref(v_es_5171_);
                        v_isSharedCheck_5215_ = (!lean_is_exclusive(v_x_5166_)) as u8;
                        if v_isSharedCheck_5215_ == 0 {
                            v_unused_5216_ = lean_ctor_get(v_x_5166_, 0);
                            lean_dec(v_unused_5216_);
                            v___x_5180_ = v_x_5166_;
                            v_isShared_5181_ = v_isSharedCheck_5215_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_5166_);
                            v___x_5180_ = lean_box(0);
                            v_isShared_5181_ = v_isSharedCheck_5215_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5217_ = lean_ctor_get(v_x_5166_, 0);
                    v_vs_5218_ = lean_ctor_get(v_x_5166_, 1);
                    v_isSharedCheck_5238_ = (!lean_is_exclusive(v_x_5166_)) as u8;
                    if v_isSharedCheck_5238_ == 0 {
                        v___x_5220_ = v_x_5166_;
                        v_isShared_5221_ = v_isSharedCheck_5238_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_5218_);
                        lean_inc(v_ks_5217_);
                        lean_dec(v_x_5166_);
                        v___x_5220_ = lean_box(0);
                        v_isShared_5221_ = v_isSharedCheck_5238_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5182_ = lean_array_fget(v_es_5171_, v_j_5176_);
                v___x_5183_ = lean_box(0);
                v_xs_x27_5184_ = lean_array_fset(v_es_5171_, v_j_5176_, v___x_5183_);
                match lean_obj_tag(v_v_5182_) {
                    0 => {
                        v_key_5191_ = lean_ctor_get(v_v_5182_, 0);
                        v_val_5192_ = lean_ctor_get(v_v_5182_, 1);
                        v_isSharedCheck_5202_ = (!lean_is_exclusive(v_v_5182_)) as u8;
                        if v_isSharedCheck_5202_ == 0 {
                            v___x_5194_ = v_v_5182_;
                            v_isShared_5195_ = v_isSharedCheck_5202_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_5192_);
                            lean_inc(v_key_5191_);
                            lean_dec(v_v_5182_);
                            v___x_5194_ = lean_box(0);
                            v_isShared_5195_ = v_isSharedCheck_5202_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5203_ = lean_ctor_get(v_v_5182_, 0);
                        v_isSharedCheck_5213_ = (!lean_is_exclusive(v_v_5182_)) as u8;
                        if v_isSharedCheck_5213_ == 0 {
                            v___x_5205_ = v_v_5182_;
                            v_isShared_5206_ = v_isSharedCheck_5213_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_5203_);
                            lean_dec(v_v_5182_);
                            v___x_5205_ = lean_box(0);
                            v_isShared_5206_ = v_isSharedCheck_5213_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5214_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5214_, 0, v_x_5169_);
                        lean_ctor_set(v___x_5214_, 1, v_x_5170_);
                        v___y_5186_ = v___x_5214_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5187_ = lean_array_fset(v_xs_x27_5184_, v_j_5176_, v___y_5186_);
                lean_dec(v_j_5176_);
                if v_isShared_5181_ == 0 {
                    lean_ctor_set(v___x_5180_, 0, v___x_5187_);
                    v___x_5189_ = v___x_5180_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___x_5187_);
                    v___x_5189_ = v_reuseFailAlloc_5190_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5189_;
            }
            4 => {
                v___x_5196_ = l_Lean_instBEqMVarId_beq(v_x_5169_, v_key_5191_);
                if v___x_5196_ == 0 {
                    lean_del_object(v___x_5194_);
                    v___x_5197_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5191_,
                        v_val_5192_,
                        v_x_5169_,
                        v_x_5170_,
                    );
                    v___x_5198_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5198_, 0, v___x_5197_);
                    v___y_5186_ = v___x_5198_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_5192_);
                    lean_dec(v_key_5191_);
                    if v_isShared_5195_ == 0 {
                        lean_ctor_set(v___x_5194_, 1, v_x_5170_);
                        lean_ctor_set(v___x_5194_, 0, v_x_5169_);
                        v___x_5200_ = v___x_5194_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5201_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_x_5169_);
                        lean_ctor_set(v_reuseFailAlloc_5201_, 1, v_x_5170_);
                        v___x_5200_ = v_reuseFailAlloc_5201_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5186_ = v___x_5200_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5207_ = lean_usize_shift_right(v_x_5167_, v___x_5172_);
                v___x_5208_ = lean_usize_add(v_x_5168_, v___x_5173_);
                v___x_5209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_node_5203_, v___x_5207_, v___x_5208_, v_x_5169_, v_x_5170_);
                if v_isShared_5206_ == 0 {
                    lean_ctor_set(v___x_5205_, 0, v___x_5209_);
                    v___x_5211_ = v___x_5205_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5212_, 0, v___x_5209_);
                    v___x_5211_ = v_reuseFailAlloc_5212_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5186_ = v___x_5211_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5221_ == 0 {
                    v___x_5223_ = v___x_5220_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_ks_5217_);
                    lean_ctor_set(v_reuseFailAlloc_5237_, 1, v_vs_5218_);
                    v___x_5223_ = v_reuseFailAlloc_5237_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5224_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(v___x_5223_, v_x_5169_, v_x_5170_);
                v___x_5232_ = 7usize;
                v___x_5233_ = lean_usize_dec_le(v___x_5232_, v_x_5168_);
                if v___x_5233_ == 0 {
                    v___x_5234_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5224_);
                    v___x_5235_ = lean_unsigned_to_nat(4);
                    v___x_5236_ = lean_nat_dec_lt(v___x_5234_, v___x_5235_);
                    lean_dec(v___x_5234_);
                    v___y_5226_ = v___x_5236_;
                    state = 10;
                    continue;
                } else {
                    v___y_5226_ = v___x_5233_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5226_ == 0 {
                    v_ks_5227_ = lean_ctor_get(v_newNode_5224_, 0);
                    lean_inc_ref(v_ks_5227_);
                    v_vs_5228_ = lean_ctor_get(v_newNode_5224_, 1);
                    lean_inc_ref(v_vs_5228_);
                    lean_dec_ref(v_newNode_5224_);
                    v___x_5229_ = lean_unsigned_to_nat(0);
                    v___x_5230_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_5231_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_x_5168_, v_ks_5227_, v_vs_5228_, v___x_5229_, v___x_5230_);
                    lean_dec_ref(v_vs_5228_);
                    lean_dec_ref(v_ks_5227_);
                    return v___x_5231_;
                } else {
                    return v_newNode_5224_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_5239_: usize,
    mut v_keys_5240_: *mut LeanObject,
    mut v_vals_5241_: *mut LeanObject,
    mut v_i_5242_: *mut LeanObject,
    mut v_entries_5243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: u8 = 0;
    let mut v_k_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: u64 = 0;
    let mut v_h_5249_: usize = 0;
    let mut v___x_5250_: usize = 0;
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: usize = 0;
    let mut v___x_5253_: usize = 0;
    let mut v___x_5254_: usize = 0;
    let mut v_h_5255_: usize = 0;
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5244_ = lean_array_get_size(v_keys_5240_);
                v___x_5245_ = lean_nat_dec_lt(v_i_5242_, v___x_5244_);
                if v___x_5245_ == 0 {
                    lean_dec(v_i_5242_);
                    return v_entries_5243_;
                } else {
                    v_k_5246_ = lean_array_fget_borrowed(v_keys_5240_, v_i_5242_);
                    v_v_5247_ = lean_array_fget_borrowed(v_vals_5241_, v_i_5242_);
                    v___x_5248_ = l_Lean_instHashableMVarId_hash(v_k_5246_);
                    v_h_5249_ = lean_uint64_to_usize(v___x_5248_);
                    v___x_5250_ = 5usize;
                    v___x_5251_ = lean_unsigned_to_nat(1);
                    v___x_5252_ = 1usize;
                    v___x_5253_ = lean_usize_sub(v_depth_5239_, v___x_5252_);
                    v___x_5254_ = lean_usize_mul(v___x_5250_, v___x_5253_);
                    v_h_5255_ = lean_usize_shift_right(v_h_5249_, v___x_5254_);
                    v___x_5256_ = lean_nat_add(v_i_5242_, v___x_5251_);
                    lean_dec(v_i_5242_);
                    lean_inc(v_v_5247_);
                    lean_inc(v_k_5246_);
                    v___x_5257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_entries_5243_, v_h_5255_, v_depth_5239_, v_k_5246_, v_v_5247_);
                    v_i_5242_ = v___x_5256_;
                    v_entries_5243_ = v___x_5257_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_5259_: *mut LeanObject,
    mut v_keys_5260_: *mut LeanObject,
    mut v_vals_5261_: *mut LeanObject,
    mut v_i_5262_: *mut LeanObject,
    mut v_entries_5263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5264_: usize = 0;
    let mut v_res_5265_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5264_ = lean_unbox_usize(v_depth_5259_);
    lean_dec(v_depth_5259_);
    v_res_5265_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_5264_, v_keys_5260_, v_vals_5261_, v_i_5262_, v_entries_5263_);
    lean_dec_ref(v_vals_5261_);
    lean_dec_ref(v_keys_5260_);
    return v_res_5265_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_5266_: *mut LeanObject,
    mut v_x_5267_: *mut LeanObject,
    mut v_x_5268_: *mut LeanObject,
    mut v_x_5269_: *mut LeanObject,
    mut v_x_5270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1695__boxed_5271_: usize = 0;
    let mut v_x_1696__boxed_5272_: usize = 0;
    let mut v_res_5273_: *mut LeanObject = core::ptr::null_mut();
    v_x_1695__boxed_5271_ = lean_unbox_usize(v_x_5267_);
    lean_dec(v_x_5267_);
    v_x_1696__boxed_5272_ = lean_unbox_usize(v_x_5268_);
    lean_dec(v_x_5268_);
    v_res_5273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_5266_, v_x_1695__boxed_5271_, v_x_1696__boxed_5272_, v_x_5269_, v_x_5270_);
    return v_res_5273_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(
    mut v_x_5274_: *mut LeanObject,
    mut v_x_5275_: *mut LeanObject,
    mut v_x_5276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5277_: u64 = 0;
    let mut v___x_5278_: usize = 0;
    let mut v___x_5279_: usize = 0;
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    v___x_5277_ = l_Lean_instHashableMVarId_hash(v_x_5275_);
    v___x_5278_ = lean_uint64_to_usize(v___x_5277_);
    v___x_5279_ = 1usize;
    v___x_5280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_5274_, v___x_5278_, v___x_5279_, v_x_5275_, v_x_5276_);
    return v___x_5280_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(
    mut v_mvarId_5281_: *mut LeanObject,
    mut v_val_5282_: *mut LeanObject,
    mut v___y_5283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v_depth_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5306_: u8 = 0;
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v_isSharedCheck_5318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5285_ = lean_st_ref_take(v___y_5283_);
                v_mctx_5286_ = lean_ctor_get(v___x_5285_, 0);
                v_cache_5287_ = lean_ctor_get(v___x_5285_, 1);
                v_zetaDeltaFVarIds_5288_ = lean_ctor_get(v___x_5285_, 2);
                v_postponed_5289_ = lean_ctor_get(v___x_5285_, 3);
                v_diag_5290_ = lean_ctor_get(v___x_5285_, 4);
                v_isSharedCheck_5318_ = (!lean_is_exclusive(v___x_5285_)) as u8;
                if v_isSharedCheck_5318_ == 0 {
                    v___x_5292_ = v___x_5285_;
                    v_isShared_5293_ = v_isSharedCheck_5318_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_5290_);
                    lean_inc(v_postponed_5289_);
                    lean_inc(v_zetaDeltaFVarIds_5288_);
                    lean_inc(v_cache_5287_);
                    lean_inc(v_mctx_5286_);
                    lean_dec(v___x_5285_);
                    v___x_5292_ = lean_box(0);
                    v_isShared_5293_ = v_isSharedCheck_5318_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_5294_ = lean_ctor_get(v_mctx_5286_, 0);
                v_levelAssignDepth_5295_ = lean_ctor_get(v_mctx_5286_, 1);
                v_lmvarCounter_5296_ = lean_ctor_get(v_mctx_5286_, 2);
                v_mvarCounter_5297_ = lean_ctor_get(v_mctx_5286_, 3);
                v_lDecls_5298_ = lean_ctor_get(v_mctx_5286_, 4);
                v_decls_5299_ = lean_ctor_get(v_mctx_5286_, 5);
                v_userNames_5300_ = lean_ctor_get(v_mctx_5286_, 6);
                v_lAssignment_5301_ = lean_ctor_get(v_mctx_5286_, 7);
                v_eAssignment_5302_ = lean_ctor_get(v_mctx_5286_, 8);
                v_dAssignment_5303_ = lean_ctor_get(v_mctx_5286_, 9);
                v_isSharedCheck_5317_ = (!lean_is_exclusive(v_mctx_5286_)) as u8;
                if v_isSharedCheck_5317_ == 0 {
                    v___x_5305_ = v_mctx_5286_;
                    v_isShared_5306_ = v_isSharedCheck_5317_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_5303_);
                    lean_inc(v_eAssignment_5302_);
                    lean_inc(v_lAssignment_5301_);
                    lean_inc(v_userNames_5300_);
                    lean_inc(v_decls_5299_);
                    lean_inc(v_lDecls_5298_);
                    lean_inc(v_mvarCounter_5297_);
                    lean_inc(v_lmvarCounter_5296_);
                    lean_inc(v_levelAssignDepth_5295_);
                    lean_inc(v_depth_5294_);
                    lean_dec(v_mctx_5286_);
                    v___x_5305_ = lean_box(0);
                    v_isShared_5306_ = v_isSharedCheck_5317_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5307_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(v_eAssignment_5302_, v_mvarId_5281_, v_val_5282_);
                if v_isShared_5306_ == 0 {
                    lean_ctor_set(v___x_5305_, 8, v___x_5307_);
                    v___x_5309_ = v___x_5305_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_depth_5294_);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 1, v_levelAssignDepth_5295_);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 2, v_lmvarCounter_5296_);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 3, v_mvarCounter_5297_);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 4, v_lDecls_5298_);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 5, v_decls_5299_);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 6, v_userNames_5300_);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 7, v_lAssignment_5301_);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 8, v___x_5307_);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 9, v_dAssignment_5303_);
                    v___x_5309_ = v_reuseFailAlloc_5316_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5293_ == 0 {
                    lean_ctor_set(v___x_5292_, 0, v___x_5309_);
                    v___x_5311_ = v___x_5292_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5309_);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 1, v_cache_5287_);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 2, v_zetaDeltaFVarIds_5288_);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 3, v_postponed_5289_);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 4, v_diag_5290_);
                    v___x_5311_ = v_reuseFailAlloc_5315_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5312_ = lean_st_ref_set(v___y_5283_, v___x_5311_);
                v___x_5313_ = lean_box(0);
                v___x_5314_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5314_, 0, v___x_5313_);
                return v___x_5314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg___boxed(
    mut v_mvarId_5319_: *mut LeanObject,
    mut v_val_5320_: *mut LeanObject,
    mut v___y_5321_: *mut LeanObject,
    mut v___y_5322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5323_: *mut LeanObject = core::ptr::null_mut();
    v_res_5323_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(
        v_mvarId_5319_,
        v_val_5320_,
        v___y_5321_,
    );
    lean_dec(v___y_5321_);
    return v_res_5323_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_updateLhs(
    mut v_lhs_x27_5324_: *mut LeanObject,
    mut v_h_5325_: *mut LeanObject,
    mut v_a_5326_: *mut LeanObject,
    mut v_a_5327_: *mut LeanObject,
    mut v_a_5328_: *mut LeanObject,
    mut v_a_5329_: *mut LeanObject,
    mut v_a_5330_: *mut LeanObject,
    mut v_a_5331_: *mut LeanObject,
    mut v_a_5332_: *mut LeanObject,
    mut v_a_5333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5356_: u8 = 0;
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5360_: u8 = 0;
    let mut v_a_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5368_: u8 = 0;
    let mut v_a_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5372_: u8 = 0;
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5376_: u8 = 0;
    let mut v_a_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5380_: u8 = 0;
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5384_: u8 = 0;
    let mut v_a_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5388_: u8 = 0;
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5392_: u8 = 0;
    let mut v_a_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5400_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5335_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_5327_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_,
                );
                if lean_obj_tag(v___x_5335_) == 0 {
                    v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
                    lean_inc(v_a_5336_);
                    lean_dec_ref_known(v___x_5335_, 1);
                    v___x_5337_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(
                        v_a_5327_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_,
                    );
                    if lean_obj_tag(v___x_5337_) == 0 {
                        v_a_5338_ = lean_ctor_get(v___x_5337_, 0);
                        lean_inc(v_a_5338_);
                        lean_dec_ref_known(v___x_5337_, 1);
                        v___x_5339_ = l_Lean_Meta_mkEq(
                            v_lhs_x27_5324_,
                            v_a_5338_,
                            v_a_5330_,
                            v_a_5331_,
                            v_a_5332_,
                            v_a_5333_,
                        );
                        if lean_obj_tag(v___x_5339_) == 0 {
                            v_a_5340_ = lean_ctor_get(v___x_5339_, 0);
                            lean_inc(v_a_5340_);
                            lean_dec_ref_known(v___x_5339_, 1);
                            lean_inc(v_a_5336_);
                            v___x_5341_ = l_Lean_MVarId_getTag(
                                v_a_5336_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_,
                            );
                            if lean_obj_tag(v___x_5341_) == 0 {
                                v_a_5342_ = lean_ctor_get(v___x_5341_, 0);
                                lean_inc(v_a_5342_);
                                lean_dec_ref_known(v___x_5341_, 1);
                                v___x_5343_ = l_Lean_mkLHSGoalRaw(v_a_5340_);
                                v___x_5344_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                    v___x_5343_,
                                    v_a_5342_,
                                    v_a_5330_,
                                    v_a_5331_,
                                    v_a_5332_,
                                    v_a_5333_,
                                );
                                if lean_obj_tag(v___x_5344_) == 0 {
                                    v_a_5345_ = lean_ctor_get(v___x_5344_, 0);
                                    lean_inc_n(v_a_5345_, 2);
                                    lean_dec_ref_known(v___x_5344_, 1);
                                    v___x_5346_ = l_Lean_Meta_mkEqTrans(
                                        v_h_5325_, v_a_5345_, v_a_5330_, v_a_5331_, v_a_5332_,
                                        v_a_5333_,
                                    );
                                    if lean_obj_tag(v___x_5346_) == 0 {
                                        v_a_5347_ = lean_ctor_get(v___x_5346_, 0);
                                        lean_inc(v_a_5347_);
                                        lean_dec_ref_known(v___x_5346_, 1);
                                        v___x_5348_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_a_5336_, v_a_5347_, v_a_5331_);
                                        lean_dec_ref(v___x_5348_);
                                        v___x_5349_ = l_Lean_Expr_mvarId_x21(v_a_5345_);
                                        lean_dec(v_a_5345_);
                                        v___x_5350_ = lean_box(0);
                                        v___x_5351_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_5351_, 0, v___x_5349_);
                                        lean_ctor_set(v___x_5351_, 1, v___x_5350_);
                                        v___x_5352_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                            v___x_5351_,
                                            v_a_5327_,
                                            v_a_5330_,
                                            v_a_5331_,
                                            v_a_5332_,
                                            v_a_5333_,
                                        );
                                        return v___x_5352_;
                                    } else {
                                        lean_dec(v_a_5345_);
                                        lean_dec(v_a_5336_);
                                        v_a_5353_ = lean_ctor_get(v___x_5346_, 0);
                                        v_isSharedCheck_5360_ =
                                            (!lean_is_exclusive(v___x_5346_)) as u8;
                                        if v_isSharedCheck_5360_ == 0 {
                                            v___x_5355_ = v___x_5346_;
                                            v_isShared_5356_ = v_isSharedCheck_5360_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5353_);
                                            lean_dec(v___x_5346_);
                                            v___x_5355_ = lean_box(0);
                                            v_isShared_5356_ = v_isSharedCheck_5360_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_5336_);
                                    lean_dec_ref(v_h_5325_);
                                    v_a_5361_ = lean_ctor_get(v___x_5344_, 0);
                                    v_isSharedCheck_5368_ = (!lean_is_exclusive(v___x_5344_)) as u8;
                                    if v_isSharedCheck_5368_ == 0 {
                                        v___x_5363_ = v___x_5344_;
                                        v_isShared_5364_ = v_isSharedCheck_5368_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5361_);
                                        lean_dec(v___x_5344_);
                                        v___x_5363_ = lean_box(0);
                                        v_isShared_5364_ = v_isSharedCheck_5368_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5340_);
                                lean_dec(v_a_5336_);
                                lean_dec_ref(v_h_5325_);
                                v_a_5369_ = lean_ctor_get(v___x_5341_, 0);
                                v_isSharedCheck_5376_ = (!lean_is_exclusive(v___x_5341_)) as u8;
                                if v_isSharedCheck_5376_ == 0 {
                                    v___x_5371_ = v___x_5341_;
                                    v_isShared_5372_ = v_isSharedCheck_5376_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_5369_);
                                    lean_dec(v___x_5341_);
                                    v___x_5371_ = lean_box(0);
                                    v_isShared_5372_ = v_isSharedCheck_5376_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5336_);
                            lean_dec_ref(v_h_5325_);
                            v_a_5377_ = lean_ctor_get(v___x_5339_, 0);
                            v_isSharedCheck_5384_ = (!lean_is_exclusive(v___x_5339_)) as u8;
                            if v_isSharedCheck_5384_ == 0 {
                                v___x_5379_ = v___x_5339_;
                                v_isShared_5380_ = v_isSharedCheck_5384_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_5377_);
                                lean_dec(v___x_5339_);
                                v___x_5379_ = lean_box(0);
                                v_isShared_5380_ = v_isSharedCheck_5384_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5336_);
                        lean_dec_ref(v_h_5325_);
                        lean_dec_ref(v_lhs_x27_5324_);
                        v_a_5385_ = lean_ctor_get(v___x_5337_, 0);
                        v_isSharedCheck_5392_ = (!lean_is_exclusive(v___x_5337_)) as u8;
                        if v_isSharedCheck_5392_ == 0 {
                            v___x_5387_ = v___x_5337_;
                            v_isShared_5388_ = v_isSharedCheck_5392_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5385_);
                            lean_dec(v___x_5337_);
                            v___x_5387_ = lean_box(0);
                            v_isShared_5388_ = v_isSharedCheck_5392_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_h_5325_);
                    lean_dec_ref(v_lhs_x27_5324_);
                    v_a_5393_ = lean_ctor_get(v___x_5335_, 0);
                    v_isSharedCheck_5400_ = (!lean_is_exclusive(v___x_5335_)) as u8;
                    if v_isSharedCheck_5400_ == 0 {
                        v___x_5395_ = v___x_5335_;
                        v_isShared_5396_ = v_isSharedCheck_5400_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5393_);
                        lean_dec(v___x_5335_);
                        v___x_5395_ = lean_box(0);
                        v_isShared_5396_ = v_isSharedCheck_5400_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5356_ == 0 {
                    v___x_5358_ = v___x_5355_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_a_5353_);
                    v___x_5358_ = v_reuseFailAlloc_5359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5358_;
            }
            3 => {
                if v_isShared_5364_ == 0 {
                    v___x_5366_ = v___x_5363_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
                    v___x_5366_ = v_reuseFailAlloc_5367_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5366_;
            }
            5 => {
                if v_isShared_5372_ == 0 {
                    v___x_5374_ = v___x_5371_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
                    v___x_5374_ = v_reuseFailAlloc_5375_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5374_;
            }
            7 => {
                if v_isShared_5380_ == 0 {
                    v___x_5382_ = v___x_5379_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
                    v___x_5382_ = v_reuseFailAlloc_5383_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5382_;
            }
            9 => {
                if v_isShared_5388_ == 0 {
                    v___x_5390_ = v___x_5387_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
                    v___x_5390_ = v_reuseFailAlloc_5391_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5390_;
            }
            11 => {
                if v_isShared_5396_ == 0 {
                    v___x_5398_ = v___x_5395_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5399_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
                    v___x_5398_ = v_reuseFailAlloc_5399_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_updateLhs___boxed(
    mut v_lhs_x27_5401_: *mut LeanObject,
    mut v_h_5402_: *mut LeanObject,
    mut v_a_5403_: *mut LeanObject,
    mut v_a_5404_: *mut LeanObject,
    mut v_a_5405_: *mut LeanObject,
    mut v_a_5406_: *mut LeanObject,
    mut v_a_5407_: *mut LeanObject,
    mut v_a_5408_: *mut LeanObject,
    mut v_a_5409_: *mut LeanObject,
    mut v_a_5410_: *mut LeanObject,
    mut v_a_5411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5412_: *mut LeanObject = core::ptr::null_mut();
    v_res_5412_ = l_Lean_Elab_Tactic_Conv_updateLhs(
        v_lhs_x27_5401_,
        v_h_5402_,
        v_a_5403_,
        v_a_5404_,
        v_a_5405_,
        v_a_5406_,
        v_a_5407_,
        v_a_5408_,
        v_a_5409_,
        v_a_5410_,
    );
    lean_dec(v_a_5410_);
    lean_dec_ref(v_a_5409_);
    lean_dec(v_a_5408_);
    lean_dec_ref(v_a_5407_);
    lean_dec(v_a_5406_);
    lean_dec_ref(v_a_5405_);
    lean_dec(v_a_5404_);
    lean_dec_ref(v_a_5403_);
    return v_res_5412_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(
    mut v_mvarId_5413_: *mut LeanObject,
    mut v_val_5414_: *mut LeanObject,
    mut v___y_5415_: *mut LeanObject,
    mut v___y_5416_: *mut LeanObject,
    mut v___y_5417_: *mut LeanObject,
    mut v___y_5418_: *mut LeanObject,
    mut v___y_5419_: *mut LeanObject,
    mut v___y_5420_: *mut LeanObject,
    mut v___y_5421_: *mut LeanObject,
    mut v___y_5422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    v___x_5424_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(
        v_mvarId_5413_,
        v_val_5414_,
        v___y_5420_,
    );
    return v___x_5424_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___boxed(
    mut v_mvarId_5425_: *mut LeanObject,
    mut v_val_5426_: *mut LeanObject,
    mut v___y_5427_: *mut LeanObject,
    mut v___y_5428_: *mut LeanObject,
    mut v___y_5429_: *mut LeanObject,
    mut v___y_5430_: *mut LeanObject,
    mut v___y_5431_: *mut LeanObject,
    mut v___y_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5436_: *mut LeanObject = core::ptr::null_mut();
    v_res_5436_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(
        v_mvarId_5425_,
        v_val_5426_,
        v___y_5427_,
        v___y_5428_,
        v___y_5429_,
        v___y_5430_,
        v___y_5431_,
        v___y_5432_,
        v___y_5433_,
        v___y_5434_,
    );
    lean_dec(v___y_5434_);
    lean_dec_ref(v___y_5433_);
    lean_dec(v___y_5432_);
    lean_dec_ref(v___y_5431_);
    lean_dec(v___y_5430_);
    lean_dec_ref(v___y_5429_);
    lean_dec(v___y_5428_);
    lean_dec_ref(v___y_5427_);
    return v_res_5436_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0(
    mut v_00_u03b2_5437_: *mut LeanObject,
    mut v_x_5438_: *mut LeanObject,
    mut v_x_5439_: *mut LeanObject,
    mut v_x_5440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    v___x_5441_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(v_x_5438_, v_x_5439_, v_x_5440_);
    return v___x_5441_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5442_: *mut LeanObject,
    mut v_x_5443_: *mut LeanObject,
    mut v_x_5444_: usize,
    mut v_x_5445_: usize,
    mut v_x_5446_: *mut LeanObject,
    mut v_x_5447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    v___x_5448_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_5443_, v_x_5444_, v_x_5445_, v_x_5446_, v_x_5447_);
    return v___x_5448_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_5449_: *mut LeanObject,
    mut v_x_5450_: *mut LeanObject,
    mut v_x_5451_: *mut LeanObject,
    mut v_x_5452_: *mut LeanObject,
    mut v_x_5453_: *mut LeanObject,
    mut v_x_5454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2089__boxed_5455_: usize = 0;
    let mut v_x_2090__boxed_5456_: usize = 0;
    let mut v_res_5457_: *mut LeanObject = core::ptr::null_mut();
    v_x_2089__boxed_5455_ = lean_unbox_usize(v_x_5451_);
    lean_dec(v_x_5451_);
    v_x_2090__boxed_5456_ = lean_unbox_usize(v_x_5452_);
    lean_dec(v_x_5452_);
    v_res_5457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(v_00_u03b2_5449_, v_x_5450_, v_x_2089__boxed_5455_, v_x_2090__boxed_5456_, v_x_5453_, v_x_5454_);
    return v_res_5457_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_5458_: *mut LeanObject,
    mut v_n_5459_: *mut LeanObject,
    mut v_k_5460_: *mut LeanObject,
    mut v_v_5461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    v___x_5462_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(v_n_5459_, v_k_5460_, v_v_5461_);
    return v___x_5462_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_5463_: *mut LeanObject,
    mut v_depth_5464_: usize,
    mut v_keys_5465_: *mut LeanObject,
    mut v_vals_5466_: *mut LeanObject,
    mut v_heq_5467_: *mut LeanObject,
    mut v_i_5468_: *mut LeanObject,
    mut v_entries_5469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    v___x_5470_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_5464_, v_keys_5465_, v_vals_5466_, v_i_5468_, v_entries_5469_);
    return v___x_5470_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_5471_: *mut LeanObject,
    mut v_depth_5472_: *mut LeanObject,
    mut v_keys_5473_: *mut LeanObject,
    mut v_vals_5474_: *mut LeanObject,
    mut v_heq_5475_: *mut LeanObject,
    mut v_i_5476_: *mut LeanObject,
    mut v_entries_5477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5478_: usize = 0;
    let mut v_res_5479_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5478_ = lean_unbox_usize(v_depth_5472_);
    lean_dec(v_depth_5472_);
    v_res_5479_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_5471_, v_depth_boxed_5478_, v_keys_5473_, v_vals_5474_, v_heq_5475_, v_i_5476_, v_entries_5477_);
    lean_dec_ref(v_vals_5474_);
    lean_dec_ref(v_keys_5473_);
    return v_res_5479_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_5480_: *mut LeanObject,
    mut v_x_5481_: *mut LeanObject,
    mut v_x_5482_: *mut LeanObject,
    mut v_x_5483_: *mut LeanObject,
    mut v_x_5484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    v___x_5485_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_5481_, v_x_5482_, v_x_5483_, v_x_5484_);
    return v___x_5485_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(
    mut v_lhs_x27_5486_: *mut LeanObject,
    mut v_a_5487_: *mut LeanObject,
    mut v___y_5488_: *mut LeanObject,
    mut v___y_5489_: *mut LeanObject,
    mut v___y_5490_: *mut LeanObject,
    mut v___y_5491_: *mut LeanObject,
    mut v___y_5492_: *mut LeanObject,
    mut v___y_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5514_: u8 = 0;
    let mut v_a_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5518_: u8 = 0;
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5522_: u8 = 0;
    let mut v_a_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5526_: u8 = 0;
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5497_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_5489_,
                    v___y_5492_,
                    v___y_5493_,
                    v___y_5494_,
                    v___y_5495_,
                );
                if lean_obj_tag(v___x_5497_) == 0 {
                    v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
                    lean_inc(v_a_5498_);
                    lean_dec_ref_known(v___x_5497_, 1);
                    v___x_5499_ = l_Lean_Meta_mkEq(
                        v_lhs_x27_5486_,
                        v_a_5487_,
                        v___y_5492_,
                        v___y_5493_,
                        v___y_5494_,
                        v___y_5495_,
                    );
                    if lean_obj_tag(v___x_5499_) == 0 {
                        v_a_5500_ = lean_ctor_get(v___x_5499_, 0);
                        lean_inc(v_a_5500_);
                        lean_dec_ref_known(v___x_5499_, 1);
                        v___x_5501_ = l_Lean_mkLHSGoalRaw(v_a_5500_);
                        v___x_5502_ = l_Lean_MVarId_replaceTargetDefEq(
                            v_a_5498_,
                            v___x_5501_,
                            v___y_5492_,
                            v___y_5493_,
                            v___y_5494_,
                            v___y_5495_,
                        );
                        if lean_obj_tag(v___x_5502_) == 0 {
                            v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
                            lean_inc(v_a_5503_);
                            lean_dec_ref_known(v___x_5502_, 1);
                            v___x_5504_ = lean_box(0);
                            v___x_5505_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_5505_, 0, v_a_5503_);
                            lean_ctor_set(v___x_5505_, 1, v___x_5504_);
                            v___x_5506_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v___x_5505_,
                                v___y_5489_,
                                v___y_5492_,
                                v___y_5493_,
                                v___y_5494_,
                                v___y_5495_,
                            );
                            return v___x_5506_;
                        } else {
                            v_a_5507_ = lean_ctor_get(v___x_5502_, 0);
                            v_isSharedCheck_5514_ = (!lean_is_exclusive(v___x_5502_)) as u8;
                            if v_isSharedCheck_5514_ == 0 {
                                v___x_5509_ = v___x_5502_;
                                v_isShared_5510_ = v_isSharedCheck_5514_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5507_);
                                lean_dec(v___x_5502_);
                                v___x_5509_ = lean_box(0);
                                v_isShared_5510_ = v_isSharedCheck_5514_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5498_);
                        v_a_5515_ = lean_ctor_get(v___x_5499_, 0);
                        v_isSharedCheck_5522_ = (!lean_is_exclusive(v___x_5499_)) as u8;
                        if v_isSharedCheck_5522_ == 0 {
                            v___x_5517_ = v___x_5499_;
                            v_isShared_5518_ = v_isSharedCheck_5522_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5515_);
                            lean_dec(v___x_5499_);
                            v___x_5517_ = lean_box(0);
                            v_isShared_5518_ = v_isSharedCheck_5522_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_5487_);
                    lean_dec_ref(v_lhs_x27_5486_);
                    v_a_5523_ = lean_ctor_get(v___x_5497_, 0);
                    v_isSharedCheck_5530_ = (!lean_is_exclusive(v___x_5497_)) as u8;
                    if v_isSharedCheck_5530_ == 0 {
                        v___x_5525_ = v___x_5497_;
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5523_);
                        lean_dec(v___x_5497_);
                        v___x_5525_ = lean_box(0);
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5510_ == 0 {
                    v___x_5512_ = v___x_5509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_a_5507_);
                    v___x_5512_ = v_reuseFailAlloc_5513_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5512_;
            }
            3 => {
                if v_isShared_5518_ == 0 {
                    v___x_5520_ = v___x_5517_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_a_5515_);
                    v___x_5520_ = v_reuseFailAlloc_5521_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5520_;
            }
            5 => {
                if v_isShared_5526_ == 0 {
                    v___x_5528_ = v___x_5525_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
                    v___x_5528_ = v_reuseFailAlloc_5529_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed(
    mut v_lhs_x27_5531_: *mut LeanObject,
    mut v_a_5532_: *mut LeanObject,
    mut v___y_5533_: *mut LeanObject,
    mut v___y_5534_: *mut LeanObject,
    mut v___y_5535_: *mut LeanObject,
    mut v___y_5536_: *mut LeanObject,
    mut v___y_5537_: *mut LeanObject,
    mut v___y_5538_: *mut LeanObject,
    mut v___y_5539_: *mut LeanObject,
    mut v___y_5540_: *mut LeanObject,
    mut v___y_5541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5542_: *mut LeanObject = core::ptr::null_mut();
    v_res_5542_ = l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(
        v_lhs_x27_5531_,
        v_a_5532_,
        v___y_5533_,
        v___y_5534_,
        v___y_5535_,
        v___y_5536_,
        v___y_5537_,
        v___y_5538_,
        v___y_5539_,
        v___y_5540_,
    );
    lean_dec(v___y_5540_);
    lean_dec_ref(v___y_5539_);
    lean_dec(v___y_5538_);
    lean_dec_ref(v___y_5537_);
    lean_dec(v___y_5536_);
    lean_dec_ref(v___y_5535_);
    lean_dec(v___y_5534_);
    lean_dec_ref(v___y_5533_);
    return v_res_5542_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_changeLhs(
    mut v_lhs_x27_5543_: *mut LeanObject,
    mut v_a_5544_: *mut LeanObject,
    mut v_a_5545_: *mut LeanObject,
    mut v_a_5546_: *mut LeanObject,
    mut v_a_5547_: *mut LeanObject,
    mut v_a_5548_: *mut LeanObject,
    mut v_a_5549_: *mut LeanObject,
    mut v_a_5550_: *mut LeanObject,
    mut v_a_5551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5560_: u8 = 0;
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5564_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5553_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(
                    v_a_5545_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_,
                );
                if lean_obj_tag(v___x_5553_) == 0 {
                    v_a_5554_ = lean_ctor_get(v___x_5553_, 0);
                    lean_inc(v_a_5554_);
                    lean_dec_ref_known(v___x_5553_, 1);
                    v___f_5555_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    lean_closure_set(v___f_5555_, 0, v_lhs_x27_5543_);
                    lean_closure_set(v___f_5555_, 1, v_a_5554_);
                    v___x_5556_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v___f_5555_,
                        v_a_5544_,
                        v_a_5545_,
                        v_a_5546_,
                        v_a_5547_,
                        v_a_5548_,
                        v_a_5549_,
                        v_a_5550_,
                        v_a_5551_,
                    );
                    return v___x_5556_;
                } else {
                    lean_dec_ref(v_lhs_x27_5543_);
                    v_a_5557_ = lean_ctor_get(v___x_5553_, 0);
                    v_isSharedCheck_5564_ = (!lean_is_exclusive(v___x_5553_)) as u8;
                    if v_isSharedCheck_5564_ == 0 {
                        v___x_5559_ = v___x_5553_;
                        v_isShared_5560_ = v_isSharedCheck_5564_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5557_);
                        lean_dec(v___x_5553_);
                        v___x_5559_ = lean_box(0);
                        v_isShared_5560_ = v_isSharedCheck_5564_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5560_ == 0 {
                    v___x_5562_ = v___x_5559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5563_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_a_5557_);
                    v___x_5562_ = v_reuseFailAlloc_5563_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_changeLhs___boxed(
    mut v_lhs_x27_5565_: *mut LeanObject,
    mut v_a_5566_: *mut LeanObject,
    mut v_a_5567_: *mut LeanObject,
    mut v_a_5568_: *mut LeanObject,
    mut v_a_5569_: *mut LeanObject,
    mut v_a_5570_: *mut LeanObject,
    mut v_a_5571_: *mut LeanObject,
    mut v_a_5572_: *mut LeanObject,
    mut v_a_5573_: *mut LeanObject,
    mut v_a_5574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5575_: *mut LeanObject = core::ptr::null_mut();
    v_res_5575_ = l_Lean_Elab_Tactic_Conv_changeLhs(
        v_lhs_x27_5565_,
        v_a_5566_,
        v_a_5567_,
        v_a_5568_,
        v_a_5569_,
        v_a_5570_,
        v_a_5571_,
        v_a_5572_,
        v_a_5573_,
    );
    lean_dec(v_a_5573_);
    lean_dec_ref(v_a_5572_);
    lean_dec(v_a_5571_);
    lean_dec_ref(v_a_5570_);
    lean_dec(v_a_5569_);
    lean_dec_ref(v_a_5568_);
    lean_dec(v_a_5567_);
    lean_dec_ref(v_a_5566_);
    return v_res_5575_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(
    mut v___y_5576_: *mut LeanObject,
    mut v___y_5577_: *mut LeanObject,
    mut v___y_5578_: *mut LeanObject,
    mut v___y_5579_: *mut LeanObject,
    mut v___y_5580_: *mut LeanObject,
    mut v___y_5581_: *mut LeanObject,
    mut v___y_5582_: *mut LeanObject,
    mut v___y_5583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5593_: u8 = 0;
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut v_a_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5601_: u8 = 0;
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5585_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_5577_,
                    v___y_5580_,
                    v___y_5581_,
                    v___y_5582_,
                    v___y_5583_,
                );
                if lean_obj_tag(v___x_5585_) == 0 {
                    v_a_5586_ = lean_ctor_get(v___x_5585_, 0);
                    lean_inc(v_a_5586_);
                    lean_dec_ref_known(v___x_5585_, 1);
                    lean_inc(v___y_5583_);
                    lean_inc_ref(v___y_5582_);
                    lean_inc(v___y_5581_);
                    lean_inc_ref(v___y_5580_);
                    v___x_5587_ = lean_whnf(
                        v_a_5586_,
                        v___y_5580_,
                        v___y_5581_,
                        v___y_5582_,
                        v___y_5583_,
                    );
                    if lean_obj_tag(v___x_5587_) == 0 {
                        v_a_5588_ = lean_ctor_get(v___x_5587_, 0);
                        lean_inc(v_a_5588_);
                        lean_dec_ref_known(v___x_5587_, 1);
                        v___x_5589_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                            v_a_5588_,
                            v___y_5576_,
                            v___y_5577_,
                            v___y_5578_,
                            v___y_5579_,
                            v___y_5580_,
                            v___y_5581_,
                            v___y_5582_,
                            v___y_5583_,
                        );
                        lean_dec(v___y_5583_);
                        lean_dec_ref(v___y_5582_);
                        lean_dec(v___y_5581_);
                        lean_dec_ref(v___y_5580_);
                        return v___x_5589_;
                    } else {
                        lean_dec(v___y_5583_);
                        lean_dec_ref(v___y_5582_);
                        lean_dec(v___y_5581_);
                        lean_dec_ref(v___y_5580_);
                        v_a_5590_ = lean_ctor_get(v___x_5587_, 0);
                        v_isSharedCheck_5597_ = (!lean_is_exclusive(v___x_5587_)) as u8;
                        if v_isSharedCheck_5597_ == 0 {
                            v___x_5592_ = v___x_5587_;
                            v_isShared_5593_ = v_isSharedCheck_5597_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5590_);
                            lean_dec(v___x_5587_);
                            v___x_5592_ = lean_box(0);
                            v_isShared_5593_ = v_isSharedCheck_5597_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_5583_);
                    lean_dec_ref(v___y_5582_);
                    lean_dec(v___y_5581_);
                    lean_dec_ref(v___y_5580_);
                    v_a_5598_ = lean_ctor_get(v___x_5585_, 0);
                    v_isSharedCheck_5605_ = (!lean_is_exclusive(v___x_5585_)) as u8;
                    if v_isSharedCheck_5605_ == 0 {
                        v___x_5600_ = v___x_5585_;
                        v_isShared_5601_ = v_isSharedCheck_5605_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5598_);
                        lean_dec(v___x_5585_);
                        v___x_5600_ = lean_box(0);
                        v_isShared_5601_ = v_isSharedCheck_5605_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5593_ == 0 {
                    v___x_5595_ = v___x_5592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5596_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_a_5590_);
                    v___x_5595_ = v_reuseFailAlloc_5596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5595_;
            }
            3 => {
                if v_isShared_5601_ == 0 {
                    v___x_5603_ = v___x_5600_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_a_5598_);
                    v___x_5603_ = v_reuseFailAlloc_5604_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0___boxed(
    mut v___y_5606_: *mut LeanObject,
    mut v___y_5607_: *mut LeanObject,
    mut v___y_5608_: *mut LeanObject,
    mut v___y_5609_: *mut LeanObject,
    mut v___y_5610_: *mut LeanObject,
    mut v___y_5611_: *mut LeanObject,
    mut v___y_5612_: *mut LeanObject,
    mut v___y_5613_: *mut LeanObject,
    mut v___y_5614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5615_: *mut LeanObject = core::ptr::null_mut();
    v_res_5615_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(
        v___y_5606_,
        v___y_5607_,
        v___y_5608_,
        v___y_5609_,
        v___y_5610_,
        v___y_5611_,
        v___y_5612_,
        v___y_5613_,
    );
    lean_dec(v___y_5609_);
    lean_dec_ref(v___y_5608_);
    lean_dec(v___y_5607_);
    lean_dec_ref(v___y_5606_);
    return v_res_5615_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(
    mut v_a_5617_: *mut LeanObject,
    mut v_a_5618_: *mut LeanObject,
    mut v_a_5619_: *mut LeanObject,
    mut v_a_5620_: *mut LeanObject,
    mut v_a_5621_: *mut LeanObject,
    mut v_a_5622_: *mut LeanObject,
    mut v_a_5623_: *mut LeanObject,
    mut v_a_5624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    v___f_5626_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0;
    v___x_5627_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_5626_,
        v_a_5617_,
        v_a_5618_,
        v_a_5619_,
        v_a_5620_,
        v_a_5621_,
        v_a_5622_,
        v_a_5623_,
        v_a_5624_,
    );
    return v___x_5627_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___boxed(
    mut v_a_5628_: *mut LeanObject,
    mut v_a_5629_: *mut LeanObject,
    mut v_a_5630_: *mut LeanObject,
    mut v_a_5631_: *mut LeanObject,
    mut v_a_5632_: *mut LeanObject,
    mut v_a_5633_: *mut LeanObject,
    mut v_a_5634_: *mut LeanObject,
    mut v_a_5635_: *mut LeanObject,
    mut v_a_5636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5637_: *mut LeanObject = core::ptr::null_mut();
    v_res_5637_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(
        v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_,
    );
    lean_dec(v_a_5635_);
    lean_dec_ref(v_a_5634_);
    lean_dec(v_a_5633_);
    lean_dec_ref(v_a_5632_);
    lean_dec(v_a_5631_);
    lean_dec_ref(v_a_5630_);
    lean_dec(v_a_5629_);
    lean_dec_ref(v_a_5628_);
    return v_res_5637_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalWhnf(
    mut v_x_5638_: *mut LeanObject,
    mut v_a_5639_: *mut LeanObject,
    mut v_a_5640_: *mut LeanObject,
    mut v_a_5641_: *mut LeanObject,
    mut v_a_5642_: *mut LeanObject,
    mut v_a_5643_: *mut LeanObject,
    mut v_a_5644_: *mut LeanObject,
    mut v_a_5645_: *mut LeanObject,
    mut v_a_5646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    v___x_5648_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(
        v_a_5639_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_,
    );
    return v___x_5648_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalWhnf___boxed(
    mut v_x_5649_: *mut LeanObject,
    mut v_a_5650_: *mut LeanObject,
    mut v_a_5651_: *mut LeanObject,
    mut v_a_5652_: *mut LeanObject,
    mut v_a_5653_: *mut LeanObject,
    mut v_a_5654_: *mut LeanObject,
    mut v_a_5655_: *mut LeanObject,
    mut v_a_5656_: *mut LeanObject,
    mut v_a_5657_: *mut LeanObject,
    mut v_a_5658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5659_: *mut LeanObject = core::ptr::null_mut();
    v_res_5659_ = l_Lean_Elab_Tactic_Conv_evalWhnf(
        v_x_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_,
        v_a_5657_,
    );
    lean_dec(v_a_5657_);
    lean_dec_ref(v_a_5656_);
    lean_dec(v_a_5655_);
    lean_dec_ref(v_a_5654_);
    lean_dec(v_a_5653_);
    lean_dec_ref(v_a_5652_);
    lean_dec(v_a_5651_);
    lean_dec_ref(v_a_5650_);
    lean_dec(v_x_5649_);
    return v_res_5659_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1()
-> *mut LeanObject {
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    v___x_5680_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5681_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5;
    v___x_5682_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8;
    v___x_5683_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalWhnf___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5684_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5680_,
        v___x_5681_,
        v___x_5682_,
        v___x_5683_,
    );
    return v___x_5684_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___boxed(
    mut v_a_5685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5686_: *mut LeanObject = core::ptr::null_mut();
    v_res_5686_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
    return v_res_5686_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3()
-> *mut LeanObject {
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    v___x_5713_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8;
    v___x_5714_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6;
    v___x_5715_ = l_Lean_addBuiltinDeclarationRanges(v___x_5713_, v___x_5714_);
    return v___x_5715_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___boxed(
    mut v_a_5716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5717_: *mut LeanObject = core::ptr::null_mut();
    v_res_5717_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
    return v_res_5717_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(
    mut v___y_5718_: *mut LeanObject,
    mut v___y_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
    mut v___y_5724_: *mut LeanObject,
    mut v___y_5725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: u8 = 0;
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5736_: u8 = 0;
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5740_: u8 = 0;
    let mut v_a_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5744_: u8 = 0;
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5727_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_5719_,
                    v___y_5722_,
                    v___y_5723_,
                    v___y_5724_,
                    v___y_5725_,
                );
                if lean_obj_tag(v___x_5727_) == 0 {
                    v_a_5728_ = lean_ctor_get(v___x_5727_, 0);
                    lean_inc(v_a_5728_);
                    lean_dec_ref_known(v___x_5727_, 1);
                    v___x_5729_ = 1;
                    v___x_5730_ = l_Lean_Meta_reduce(
                        v_a_5728_,
                        v___x_5729_,
                        v___x_5729_,
                        v___x_5729_,
                        v___y_5722_,
                        v___y_5723_,
                        v___y_5724_,
                        v___y_5725_,
                    );
                    if lean_obj_tag(v___x_5730_) == 0 {
                        v_a_5731_ = lean_ctor_get(v___x_5730_, 0);
                        lean_inc(v_a_5731_);
                        lean_dec_ref_known(v___x_5730_, 1);
                        v___x_5732_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                            v_a_5731_,
                            v___y_5718_,
                            v___y_5719_,
                            v___y_5720_,
                            v___y_5721_,
                            v___y_5722_,
                            v___y_5723_,
                            v___y_5724_,
                            v___y_5725_,
                        );
                        return v___x_5732_;
                    } else {
                        v_a_5733_ = lean_ctor_get(v___x_5730_, 0);
                        v_isSharedCheck_5740_ = (!lean_is_exclusive(v___x_5730_)) as u8;
                        if v_isSharedCheck_5740_ == 0 {
                            v___x_5735_ = v___x_5730_;
                            v_isShared_5736_ = v_isSharedCheck_5740_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5733_);
                            lean_dec(v___x_5730_);
                            v___x_5735_ = lean_box(0);
                            v_isShared_5736_ = v_isSharedCheck_5740_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_5741_ = lean_ctor_get(v___x_5727_, 0);
                    v_isSharedCheck_5748_ = (!lean_is_exclusive(v___x_5727_)) as u8;
                    if v_isSharedCheck_5748_ == 0 {
                        v___x_5743_ = v___x_5727_;
                        v_isShared_5744_ = v_isSharedCheck_5748_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5741_);
                        lean_dec(v___x_5727_);
                        v___x_5743_ = lean_box(0);
                        v_isShared_5744_ = v_isSharedCheck_5748_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5736_ == 0 {
                    v___x_5738_ = v___x_5735_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5739_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5739_, 0, v_a_5733_);
                    v___x_5738_ = v_reuseFailAlloc_5739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5738_;
            }
            3 => {
                if v_isShared_5744_ == 0 {
                    v___x_5746_ = v___x_5743_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5747_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5747_, 0, v_a_5741_);
                    v___x_5746_ = v_reuseFailAlloc_5747_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed(
    mut v___y_5749_: *mut LeanObject,
    mut v___y_5750_: *mut LeanObject,
    mut v___y_5751_: *mut LeanObject,
    mut v___y_5752_: *mut LeanObject,
    mut v___y_5753_: *mut LeanObject,
    mut v___y_5754_: *mut LeanObject,
    mut v___y_5755_: *mut LeanObject,
    mut v___y_5756_: *mut LeanObject,
    mut v___y_5757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5758_: *mut LeanObject = core::ptr::null_mut();
    v_res_5758_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(
        v___y_5749_,
        v___y_5750_,
        v___y_5751_,
        v___y_5752_,
        v___y_5753_,
        v___y_5754_,
        v___y_5755_,
        v___y_5756_,
    );
    lean_dec(v___y_5756_);
    lean_dec_ref(v___y_5755_);
    lean_dec(v___y_5754_);
    lean_dec_ref(v___y_5753_);
    lean_dec(v___y_5752_);
    lean_dec_ref(v___y_5751_);
    lean_dec(v___y_5750_);
    lean_dec_ref(v___y_5749_);
    return v_res_5758_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalReduce___redArg(
    mut v_a_5760_: *mut LeanObject,
    mut v_a_5761_: *mut LeanObject,
    mut v_a_5762_: *mut LeanObject,
    mut v_a_5763_: *mut LeanObject,
    mut v_a_5764_: *mut LeanObject,
    mut v_a_5765_: *mut LeanObject,
    mut v_a_5766_: *mut LeanObject,
    mut v_a_5767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    v___f_5769_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0;
    v___x_5770_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_5769_,
        v_a_5760_,
        v_a_5761_,
        v_a_5762_,
        v_a_5763_,
        v_a_5764_,
        v_a_5765_,
        v_a_5766_,
        v_a_5767_,
    );
    return v___x_5770_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalReduce___redArg___boxed(
    mut v_a_5771_: *mut LeanObject,
    mut v_a_5772_: *mut LeanObject,
    mut v_a_5773_: *mut LeanObject,
    mut v_a_5774_: *mut LeanObject,
    mut v_a_5775_: *mut LeanObject,
    mut v_a_5776_: *mut LeanObject,
    mut v_a_5777_: *mut LeanObject,
    mut v_a_5778_: *mut LeanObject,
    mut v_a_5779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5780_: *mut LeanObject = core::ptr::null_mut();
    v_res_5780_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg(
        v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_, v_a_5778_,
    );
    lean_dec(v_a_5778_);
    lean_dec_ref(v_a_5777_);
    lean_dec(v_a_5776_);
    lean_dec_ref(v_a_5775_);
    lean_dec(v_a_5774_);
    lean_dec_ref(v_a_5773_);
    lean_dec(v_a_5772_);
    lean_dec_ref(v_a_5771_);
    return v_res_5780_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalReduce(
    mut v_x_5781_: *mut LeanObject,
    mut v_a_5782_: *mut LeanObject,
    mut v_a_5783_: *mut LeanObject,
    mut v_a_5784_: *mut LeanObject,
    mut v_a_5785_: *mut LeanObject,
    mut v_a_5786_: *mut LeanObject,
    mut v_a_5787_: *mut LeanObject,
    mut v_a_5788_: *mut LeanObject,
    mut v_a_5789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    v___x_5791_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg(
        v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_,
    );
    return v___x_5791_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalReduce___boxed(
    mut v_x_5792_: *mut LeanObject,
    mut v_a_5793_: *mut LeanObject,
    mut v_a_5794_: *mut LeanObject,
    mut v_a_5795_: *mut LeanObject,
    mut v_a_5796_: *mut LeanObject,
    mut v_a_5797_: *mut LeanObject,
    mut v_a_5798_: *mut LeanObject,
    mut v_a_5799_: *mut LeanObject,
    mut v_a_5800_: *mut LeanObject,
    mut v_a_5801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5802_: *mut LeanObject = core::ptr::null_mut();
    v_res_5802_ = l_Lean_Elab_Tactic_Conv_evalReduce(
        v_x_5792_, v_a_5793_, v_a_5794_, v_a_5795_, v_a_5796_, v_a_5797_, v_a_5798_, v_a_5799_,
        v_a_5800_,
    );
    lean_dec(v_a_5800_);
    lean_dec_ref(v_a_5799_);
    lean_dec(v_a_5798_);
    lean_dec_ref(v_a_5797_);
    lean_dec(v_a_5796_);
    lean_dec_ref(v_a_5795_);
    lean_dec(v_a_5794_);
    lean_dec_ref(v_a_5793_);
    lean_dec(v_x_5792_);
    return v_res_5802_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1()
-> *mut LeanObject {
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    v___x_5818_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5819_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1;
    v___x_5820_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3;
    v___x_5821_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalReduce___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5822_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5818_,
        v___x_5819_,
        v___x_5820_,
        v___x_5821_,
    );
    return v___x_5822_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___boxed(
    mut v_a_5823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5824_: *mut LeanObject = core::ptr::null_mut();
    v_res_5824_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
    return v_res_5824_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3()
-> *mut LeanObject {
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    v___x_5851_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3;
    v___x_5852_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6;
    v___x_5853_ = l_Lean_addBuiltinDeclarationRanges(v___x_5851_, v___x_5852_);
    return v___x_5853_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___boxed(
    mut v_a_5854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5855_: *mut LeanObject = core::ptr::null_mut();
    v_res_5855_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
    return v_res_5855_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(
    mut v___y_5856_: *mut LeanObject,
    mut v___y_5857_: *mut LeanObject,
    mut v___y_5858_: *mut LeanObject,
    mut v___y_5859_: *mut LeanObject,
    mut v___y_5860_: *mut LeanObject,
    mut v___y_5861_: *mut LeanObject,
    mut v___y_5862_: *mut LeanObject,
    mut v___y_5863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: u8 = 0;
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5874_: u8 = 0;
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5878_: u8 = 0;
    let mut v_a_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5882_: u8 = 0;
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5865_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_5857_,
                    v___y_5860_,
                    v___y_5861_,
                    v___y_5862_,
                    v___y_5863_,
                );
                if lean_obj_tag(v___x_5865_) == 0 {
                    v_a_5866_ = lean_ctor_get(v___x_5865_, 0);
                    lean_inc(v_a_5866_);
                    lean_dec_ref_known(v___x_5865_, 1);
                    v___x_5867_ = 1;
                    v___x_5868_ = l_Lean_Meta_zetaReduce(
                        v_a_5866_,
                        v___x_5867_,
                        v___x_5867_,
                        v___x_5867_,
                        v___y_5860_,
                        v___y_5861_,
                        v___y_5862_,
                        v___y_5863_,
                    );
                    if lean_obj_tag(v___x_5868_) == 0 {
                        v_a_5869_ = lean_ctor_get(v___x_5868_, 0);
                        lean_inc(v_a_5869_);
                        lean_dec_ref_known(v___x_5868_, 1);
                        v___x_5870_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                            v_a_5869_,
                            v___y_5856_,
                            v___y_5857_,
                            v___y_5858_,
                            v___y_5859_,
                            v___y_5860_,
                            v___y_5861_,
                            v___y_5862_,
                            v___y_5863_,
                        );
                        return v___x_5870_;
                    } else {
                        v_a_5871_ = lean_ctor_get(v___x_5868_, 0);
                        v_isSharedCheck_5878_ = (!lean_is_exclusive(v___x_5868_)) as u8;
                        if v_isSharedCheck_5878_ == 0 {
                            v___x_5873_ = v___x_5868_;
                            v_isShared_5874_ = v_isSharedCheck_5878_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5871_);
                            lean_dec(v___x_5868_);
                            v___x_5873_ = lean_box(0);
                            v_isShared_5874_ = v_isSharedCheck_5878_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_5879_ = lean_ctor_get(v___x_5865_, 0);
                    v_isSharedCheck_5886_ = (!lean_is_exclusive(v___x_5865_)) as u8;
                    if v_isSharedCheck_5886_ == 0 {
                        v___x_5881_ = v___x_5865_;
                        v_isShared_5882_ = v_isSharedCheck_5886_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5879_);
                        lean_dec(v___x_5865_);
                        v___x_5881_ = lean_box(0);
                        v_isShared_5882_ = v_isSharedCheck_5886_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5874_ == 0 {
                    v___x_5876_ = v___x_5873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
                    v___x_5876_ = v_reuseFailAlloc_5877_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5876_;
            }
            3 => {
                if v_isShared_5882_ == 0 {
                    v___x_5884_ = v___x_5881_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5885_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_a_5879_);
                    v___x_5884_ = v_reuseFailAlloc_5885_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed(
    mut v___y_5887_: *mut LeanObject,
    mut v___y_5888_: *mut LeanObject,
    mut v___y_5889_: *mut LeanObject,
    mut v___y_5890_: *mut LeanObject,
    mut v___y_5891_: *mut LeanObject,
    mut v___y_5892_: *mut LeanObject,
    mut v___y_5893_: *mut LeanObject,
    mut v___y_5894_: *mut LeanObject,
    mut v___y_5895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5896_: *mut LeanObject = core::ptr::null_mut();
    v_res_5896_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(
        v___y_5887_,
        v___y_5888_,
        v___y_5889_,
        v___y_5890_,
        v___y_5891_,
        v___y_5892_,
        v___y_5893_,
        v___y_5894_,
    );
    lean_dec(v___y_5894_);
    lean_dec_ref(v___y_5893_);
    lean_dec(v___y_5892_);
    lean_dec_ref(v___y_5891_);
    lean_dec(v___y_5890_);
    lean_dec_ref(v___y_5889_);
    lean_dec(v___y_5888_);
    lean_dec_ref(v___y_5887_);
    return v_res_5896_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalZeta___redArg(
    mut v_a_5898_: *mut LeanObject,
    mut v_a_5899_: *mut LeanObject,
    mut v_a_5900_: *mut LeanObject,
    mut v_a_5901_: *mut LeanObject,
    mut v_a_5902_: *mut LeanObject,
    mut v_a_5903_: *mut LeanObject,
    mut v_a_5904_: *mut LeanObject,
    mut v_a_5905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    v___f_5907_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0;
    v___x_5908_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_5907_,
        v_a_5898_,
        v_a_5899_,
        v_a_5900_,
        v_a_5901_,
        v_a_5902_,
        v_a_5903_,
        v_a_5904_,
        v_a_5905_,
    );
    return v___x_5908_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalZeta___redArg___boxed(
    mut v_a_5909_: *mut LeanObject,
    mut v_a_5910_: *mut LeanObject,
    mut v_a_5911_: *mut LeanObject,
    mut v_a_5912_: *mut LeanObject,
    mut v_a_5913_: *mut LeanObject,
    mut v_a_5914_: *mut LeanObject,
    mut v_a_5915_: *mut LeanObject,
    mut v_a_5916_: *mut LeanObject,
    mut v_a_5917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5918_: *mut LeanObject = core::ptr::null_mut();
    v_res_5918_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg(
        v_a_5909_, v_a_5910_, v_a_5911_, v_a_5912_, v_a_5913_, v_a_5914_, v_a_5915_, v_a_5916_,
    );
    lean_dec(v_a_5916_);
    lean_dec_ref(v_a_5915_);
    lean_dec(v_a_5914_);
    lean_dec_ref(v_a_5913_);
    lean_dec(v_a_5912_);
    lean_dec_ref(v_a_5911_);
    lean_dec(v_a_5910_);
    lean_dec_ref(v_a_5909_);
    return v_res_5918_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalZeta(
    mut v_x_5919_: *mut LeanObject,
    mut v_a_5920_: *mut LeanObject,
    mut v_a_5921_: *mut LeanObject,
    mut v_a_5922_: *mut LeanObject,
    mut v_a_5923_: *mut LeanObject,
    mut v_a_5924_: *mut LeanObject,
    mut v_a_5925_: *mut LeanObject,
    mut v_a_5926_: *mut LeanObject,
    mut v_a_5927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    v___x_5929_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg(
        v_a_5920_, v_a_5921_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_,
    );
    return v___x_5929_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalZeta___boxed(
    mut v_x_5930_: *mut LeanObject,
    mut v_a_5931_: *mut LeanObject,
    mut v_a_5932_: *mut LeanObject,
    mut v_a_5933_: *mut LeanObject,
    mut v_a_5934_: *mut LeanObject,
    mut v_a_5935_: *mut LeanObject,
    mut v_a_5936_: *mut LeanObject,
    mut v_a_5937_: *mut LeanObject,
    mut v_a_5938_: *mut LeanObject,
    mut v_a_5939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5940_: *mut LeanObject = core::ptr::null_mut();
    v_res_5940_ = l_Lean_Elab_Tactic_Conv_evalZeta(
        v_x_5930_, v_a_5931_, v_a_5932_, v_a_5933_, v_a_5934_, v_a_5935_, v_a_5936_, v_a_5937_,
        v_a_5938_,
    );
    lean_dec(v_a_5938_);
    lean_dec_ref(v_a_5937_);
    lean_dec(v_a_5936_);
    lean_dec_ref(v_a_5935_);
    lean_dec(v_a_5934_);
    lean_dec_ref(v_a_5933_);
    lean_dec(v_a_5932_);
    lean_dec_ref(v_a_5931_);
    lean_dec(v_x_5930_);
    return v_res_5940_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1()
-> *mut LeanObject {
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    v___x_5956_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5957_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1;
    v___x_5958_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3;
    v___x_5959_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalZeta___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5960_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5956_,
        v___x_5957_,
        v___x_5958_,
        v___x_5959_,
    );
    return v___x_5960_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___boxed(
    mut v_a_5961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5962_: *mut LeanObject = core::ptr::null_mut();
    v_res_5962_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
    return v_res_5962_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3()
-> *mut LeanObject {
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    v___x_5989_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3;
    v___x_5990_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6;
    v___x_5991_ = l_Lean_addBuiltinDeclarationRanges(v___x_5989_, v___x_5990_);
    return v___x_5991_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___boxed(
    mut v_a_5992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5993_: *mut LeanObject = core::ptr::null_mut();
    v_res_5993_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
    return v_res_5993_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(
    mut v_e_5994_: *mut LeanObject,
    mut v___y_5995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5997_: u8 = 0;
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6011_: u8 = 0;
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6017_: u8 = 0;
    let mut v_unused_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5997_ = l_Lean_Expr_hasMVar(v_e_5994_);
                if v___x_5997_ == 0 {
                    v___x_5998_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5998_, 0, v_e_5994_);
                    return v___x_5998_;
                } else {
                    v___x_5999_ = lean_st_ref_get(v___y_5995_);
                    v_mctx_6000_ = lean_ctor_get(v___x_5999_, 0);
                    lean_inc_ref(v_mctx_6000_);
                    lean_dec(v___x_5999_);
                    v___x_6001_ = l_Lean_instantiateMVarsCore(v_mctx_6000_, v_e_5994_);
                    v_fst_6002_ = lean_ctor_get(v___x_6001_, 0);
                    lean_inc(v_fst_6002_);
                    v_snd_6003_ = lean_ctor_get(v___x_6001_, 1);
                    lean_inc(v_snd_6003_);
                    lean_dec_ref(v___x_6001_);
                    v___x_6004_ = lean_st_ref_take(v___y_5995_);
                    v_cache_6005_ = lean_ctor_get(v___x_6004_, 1);
                    v_zetaDeltaFVarIds_6006_ = lean_ctor_get(v___x_6004_, 2);
                    v_postponed_6007_ = lean_ctor_get(v___x_6004_, 3);
                    v_diag_6008_ = lean_ctor_get(v___x_6004_, 4);
                    v_isSharedCheck_6017_ = (!lean_is_exclusive(v___x_6004_)) as u8;
                    if v_isSharedCheck_6017_ == 0 {
                        v_unused_6018_ = lean_ctor_get(v___x_6004_, 0);
                        lean_dec(v_unused_6018_);
                        v___x_6010_ = v___x_6004_;
                        v_isShared_6011_ = v_isSharedCheck_6017_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_6008_);
                        lean_inc(v_postponed_6007_);
                        lean_inc(v_zetaDeltaFVarIds_6006_);
                        lean_inc(v_cache_6005_);
                        lean_dec(v___x_6004_);
                        v___x_6010_ = lean_box(0);
                        v_isShared_6011_ = v_isSharedCheck_6017_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6011_ == 0 {
                    lean_ctor_set(v___x_6010_, 0, v_snd_6003_);
                    v___x_6013_ = v___x_6010_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6016_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_snd_6003_);
                    lean_ctor_set(v_reuseFailAlloc_6016_, 1, v_cache_6005_);
                    lean_ctor_set(v_reuseFailAlloc_6016_, 2, v_zetaDeltaFVarIds_6006_);
                    lean_ctor_set(v_reuseFailAlloc_6016_, 3, v_postponed_6007_);
                    lean_ctor_set(v_reuseFailAlloc_6016_, 4, v_diag_6008_);
                    v___x_6013_ = v_reuseFailAlloc_6016_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6014_ = lean_st_ref_set(v___y_5995_, v___x_6013_);
                v___x_6015_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6015_, 0, v_fst_6002_);
                return v___x_6015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg___boxed(
    mut v_e_6019_: *mut LeanObject,
    mut v___y_6020_: *mut LeanObject,
    mut v___y_6021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6022_: *mut LeanObject = core::ptr::null_mut();
    v_res_6022_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(
        v_e_6019_,
        v___y_6020_,
    );
    lean_dec(v___y_6020_);
    return v_res_6022_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0(
    mut v_e_6023_: *mut LeanObject,
    mut v___y_6024_: *mut LeanObject,
    mut v___y_6025_: *mut LeanObject,
    mut v___y_6026_: *mut LeanObject,
    mut v___y_6027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    v___x_6029_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(
        v_e_6023_,
        v___y_6025_,
    );
    return v___x_6029_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___boxed(
    mut v_e_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
    mut v___y_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
    mut v___y_6034_: *mut LeanObject,
    mut v___y_6035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6036_: *mut LeanObject = core::ptr::null_mut();
    v_res_6036_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0(
        v_e_6030_,
        v___y_6031_,
        v___y_6032_,
        v___y_6033_,
        v___y_6034_,
    );
    lean_dec(v___y_6034_);
    lean_dec_ref(v___y_6033_);
    lean_dec(v___y_6032_);
    lean_dec_ref(v___y_6031_);
    return v_res_6036_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_convClear(
    mut v_mvarId_6037_: *mut LeanObject,
    mut v_fvarId_6038_: *mut LeanObject,
    mut v_a_6039_: *mut LeanObject,
    mut v_a_6040_: *mut LeanObject,
    mut v_a_6041_: *mut LeanObject,
    mut v_a_6042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: u8 = 0;
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: u8 = 0;
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_a_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6077_: u8 = 0;
    let mut v___x_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6081_: u8 = 0;
    let mut v_a_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6085_: u8 = 0;
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6089_: u8 = 0;
    let mut v_a_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6093_: u8 = 0;
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_6037_);
                v___x_6044_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(
                    v_mvarId_6037_,
                    v_a_6039_,
                    v_a_6040_,
                    v_a_6041_,
                    v_a_6042_,
                );
                if lean_obj_tag(v___x_6044_) == 0 {
                    v_a_6045_ = lean_ctor_get(v___x_6044_, 0);
                    lean_inc(v_a_6045_);
                    lean_dec_ref_known(v___x_6044_, 1);
                    v_fst_6046_ = lean_ctor_get(v_a_6045_, 0);
                    lean_inc(v_fst_6046_);
                    v_snd_6047_ = lean_ctor_get(v_a_6045_, 1);
                    lean_inc(v_snd_6047_);
                    lean_dec(v_a_6045_);
                    v___x_6048_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(v_snd_6047_, v_a_6040_);
                    v_a_6049_ = lean_ctor_get(v___x_6048_, 0);
                    lean_inc(v_a_6049_);
                    lean_dec_ref(v___x_6048_);
                    v___x_6050_ = l_Lean_Expr_isMVar(v_a_6049_);
                    if v___x_6050_ == 0 {
                        lean_dec(v_a_6049_);
                        lean_dec(v_fst_6046_);
                        v___x_6051_ = l_Lean_MVarId_clear(
                            v_mvarId_6037_,
                            v_fvarId_6038_,
                            v_a_6039_,
                            v_a_6040_,
                            v_a_6041_,
                            v_a_6042_,
                        );
                        return v___x_6051_;
                    } else {
                        v___x_6052_ = l_Lean_Expr_mvarId_x21(v_a_6049_);
                        lean_dec(v_a_6049_);
                        lean_inc(v___x_6052_);
                        v___x_6053_ = l_Lean_MVarId_getKind(
                            v___x_6052_,
                            v_a_6039_,
                            v_a_6040_,
                            v_a_6041_,
                            v_a_6042_,
                        );
                        if lean_obj_tag(v___x_6053_) == 0 {
                            v_a_6054_ = lean_ctor_get(v___x_6053_, 0);
                            lean_inc(v_a_6054_);
                            lean_dec_ref_known(v___x_6053_, 1);
                            lean_inc(v_fvarId_6038_);
                            v___x_6055_ = l_Lean_MVarId_clear(
                                v___x_6052_,
                                v_fvarId_6038_,
                                v_a_6039_,
                                v_a_6040_,
                                v_a_6041_,
                                v_a_6042_,
                            );
                            if lean_obj_tag(v___x_6055_) == 0 {
                                v_a_6056_ = lean_ctor_get(v___x_6055_, 0);
                                lean_inc_n(v_a_6056_, 2);
                                lean_dec_ref_known(v___x_6055_, 1);
                                v___x_6057_ = (lean_unbox(v_a_6054_) as u8);
                                lean_dec(v_a_6054_);
                                v___x_6058_ = l_Lean_MVarId_setKind___redArg(
                                    v_a_6056_,
                                    v___x_6057_,
                                    v_a_6040_,
                                );
                                if lean_obj_tag(v___x_6058_) == 0 {
                                    lean_dec_ref_known(v___x_6058_, 1);
                                    v___x_6059_ = l_Lean_mkMVar(v_a_6056_);
                                    v___x_6060_ = l_Lean_Meta_mkEq(
                                        v_fst_6046_,
                                        v___x_6059_,
                                        v_a_6039_,
                                        v_a_6040_,
                                        v_a_6041_,
                                        v_a_6042_,
                                    );
                                    if lean_obj_tag(v___x_6060_) == 0 {
                                        v_a_6061_ = lean_ctor_get(v___x_6060_, 0);
                                        lean_inc(v_a_6061_);
                                        lean_dec_ref_known(v___x_6060_, 1);
                                        v___x_6062_ = l_Lean_mkLHSGoalRaw(v_a_6061_);
                                        v___x_6063_ = l_Lean_MVarId_replaceTargetDefEq(
                                            v_mvarId_6037_,
                                            v___x_6062_,
                                            v_a_6039_,
                                            v_a_6040_,
                                            v_a_6041_,
                                            v_a_6042_,
                                        );
                                        if lean_obj_tag(v___x_6063_) == 0 {
                                            v_a_6064_ = lean_ctor_get(v___x_6063_, 0);
                                            lean_inc(v_a_6064_);
                                            lean_dec_ref_known(v___x_6063_, 1);
                                            v___x_6065_ = l_Lean_MVarId_clear(
                                                v_a_6064_,
                                                v_fvarId_6038_,
                                                v_a_6039_,
                                                v_a_6040_,
                                                v_a_6041_,
                                                v_a_6042_,
                                            );
                                            return v___x_6065_;
                                        } else {
                                            lean_dec(v_fvarId_6038_);
                                            return v___x_6063_;
                                        }
                                    } else {
                                        lean_dec(v_fvarId_6038_);
                                        lean_dec(v_mvarId_6037_);
                                        v_a_6066_ = lean_ctor_get(v___x_6060_, 0);
                                        v_isSharedCheck_6073_ =
                                            (!lean_is_exclusive(v___x_6060_)) as u8;
                                        if v_isSharedCheck_6073_ == 0 {
                                            v___x_6068_ = v___x_6060_;
                                            v_isShared_6069_ = v_isSharedCheck_6073_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6066_);
                                            lean_dec(v___x_6060_);
                                            v___x_6068_ = lean_box(0);
                                            v_isShared_6069_ = v_isSharedCheck_6073_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_6056_);
                                    lean_dec(v_fst_6046_);
                                    lean_dec(v_fvarId_6038_);
                                    lean_dec(v_mvarId_6037_);
                                    v_a_6074_ = lean_ctor_get(v___x_6058_, 0);
                                    v_isSharedCheck_6081_ = (!lean_is_exclusive(v___x_6058_)) as u8;
                                    if v_isSharedCheck_6081_ == 0 {
                                        v___x_6076_ = v___x_6058_;
                                        v_isShared_6077_ = v_isSharedCheck_6081_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6074_);
                                        lean_dec(v___x_6058_);
                                        v___x_6076_ = lean_box(0);
                                        v_isShared_6077_ = v_isSharedCheck_6081_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_6054_);
                                lean_dec(v_fst_6046_);
                                lean_dec(v_fvarId_6038_);
                                lean_dec(v_mvarId_6037_);
                                return v___x_6055_;
                            }
                        } else {
                            lean_dec(v___x_6052_);
                            lean_dec(v_fst_6046_);
                            lean_dec(v_fvarId_6038_);
                            lean_dec(v_mvarId_6037_);
                            v_a_6082_ = lean_ctor_get(v___x_6053_, 0);
                            v_isSharedCheck_6089_ = (!lean_is_exclusive(v___x_6053_)) as u8;
                            if v_isSharedCheck_6089_ == 0 {
                                v___x_6084_ = v___x_6053_;
                                v_isShared_6085_ = v_isSharedCheck_6089_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6082_);
                                lean_dec(v___x_6053_);
                                v___x_6084_ = lean_box(0);
                                v_isShared_6085_ = v_isSharedCheck_6089_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_fvarId_6038_);
                    lean_dec(v_mvarId_6037_);
                    v_a_6090_ = lean_ctor_get(v___x_6044_, 0);
                    v_isSharedCheck_6097_ = (!lean_is_exclusive(v___x_6044_)) as u8;
                    if v_isSharedCheck_6097_ == 0 {
                        v___x_6092_ = v___x_6044_;
                        v_isShared_6093_ = v_isSharedCheck_6097_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_6090_);
                        lean_dec(v___x_6044_);
                        v___x_6092_ = lean_box(0);
                        v_isShared_6093_ = v_isSharedCheck_6097_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6069_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
                    v___x_6071_ = v_reuseFailAlloc_6072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6071_;
            }
            3 => {
                if v_isShared_6077_ == 0 {
                    v___x_6079_ = v___x_6076_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6080_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6080_, 0, v_a_6074_);
                    v___x_6079_ = v_reuseFailAlloc_6080_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6079_;
            }
            5 => {
                if v_isShared_6085_ == 0 {
                    v___x_6087_ = v___x_6084_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6088_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6088_, 0, v_a_6082_);
                    v___x_6087_ = v_reuseFailAlloc_6088_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6087_;
            }
            7 => {
                if v_isShared_6093_ == 0 {
                    v___x_6095_ = v___x_6092_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6096_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6096_, 0, v_a_6090_);
                    v___x_6095_ = v_reuseFailAlloc_6096_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_convClear___boxed(
    mut v_mvarId_6098_: *mut LeanObject,
    mut v_fvarId_6099_: *mut LeanObject,
    mut v_a_6100_: *mut LeanObject,
    mut v_a_6101_: *mut LeanObject,
    mut v_a_6102_: *mut LeanObject,
    mut v_a_6103_: *mut LeanObject,
    mut v_a_6104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6105_: *mut LeanObject = core::ptr::null_mut();
    v_res_6105_ = l_Lean_Elab_Tactic_Conv_convClear(
        v_mvarId_6098_,
        v_fvarId_6099_,
        v_a_6100_,
        v_a_6101_,
        v_a_6102_,
        v_a_6103_,
    );
    lean_dec(v_a_6103_);
    lean_dec_ref(v_a_6102_);
    lean_dec(v_a_6101_);
    lean_dec_ref(v_a_6100_);
    return v_res_6105_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    v___x_6106_ = lean_box(0);
    v___x_6107_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_6108_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6108_, 0, v___x_6107_);
    lean_ctor_set(v___x_6108_, 1, v___x_6106_);
    return v___x_6108_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut LeanObject = core::ptr::null_mut();
    v___x_6110_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0);
    v___x_6111_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6111_, 0, v___x_6110_);
    return v___x_6111_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___boxed(
    mut v___y_6112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6113_: *mut LeanObject = core::ptr::null_mut();
    v_res_6113_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
    return v_res_6113_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(
    mut v_00_u03b1_6114_: *mut LeanObject,
    mut v___y_6115_: *mut LeanObject,
    mut v___y_6116_: *mut LeanObject,
    mut v___y_6117_: *mut LeanObject,
    mut v___y_6118_: *mut LeanObject,
    mut v___y_6119_: *mut LeanObject,
    mut v___y_6120_: *mut LeanObject,
    mut v___y_6121_: *mut LeanObject,
    mut v___y_6122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    v___x_6124_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
    return v___x_6124_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___boxed(
    mut v_00_u03b1_6125_: *mut LeanObject,
    mut v___y_6126_: *mut LeanObject,
    mut v___y_6127_: *mut LeanObject,
    mut v___y_6128_: *mut LeanObject,
    mut v___y_6129_: *mut LeanObject,
    mut v___y_6130_: *mut LeanObject,
    mut v___y_6131_: *mut LeanObject,
    mut v___y_6132_: *mut LeanObject,
    mut v___y_6133_: *mut LeanObject,
    mut v___y_6134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6135_: *mut LeanObject = core::ptr::null_mut();
    v_res_6135_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(
            v_00_u03b1_6125_,
            v___y_6126_,
            v___y_6127_,
            v___y_6128_,
            v___y_6129_,
            v___y_6130_,
            v___y_6131_,
            v___y_6132_,
            v___y_6133_,
        );
    lean_dec(v___y_6133_);
    lean_dec_ref(v___y_6132_);
    lean_dec(v___y_6131_);
    lean_dec_ref(v___y_6130_);
    lean_dec(v___y_6129_);
    lean_dec_ref(v___y_6128_);
    lean_dec(v___y_6127_);
    lean_dec_ref(v___y_6126_);
    return v_res_6135_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalClear___lam__0(
    mut v_a_6136_: *mut LeanObject,
    mut v___y_6137_: *mut LeanObject,
    mut v___y_6138_: *mut LeanObject,
    mut v___y_6139_: *mut LeanObject,
    mut v___y_6140_: *mut LeanObject,
    mut v___y_6141_: *mut LeanObject,
    mut v___y_6142_: *mut LeanObject,
    mut v___y_6143_: *mut LeanObject,
    mut v___y_6144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    v___x_6146_ = l_Lean_Meta_sortFVarIds___redArg(v_a_6136_, v___y_6141_);
    return v___x_6146_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed(
    mut v_a_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
    mut v___y_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
    mut v___y_6151_: *mut LeanObject,
    mut v___y_6152_: *mut LeanObject,
    mut v___y_6153_: *mut LeanObject,
    mut v___y_6154_: *mut LeanObject,
    mut v___y_6155_: *mut LeanObject,
    mut v___y_6156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6157_: *mut LeanObject = core::ptr::null_mut();
    v_res_6157_ = l_Lean_Elab_Tactic_Conv_evalClear___lam__0(
        v_a_6147_,
        v___y_6148_,
        v___y_6149_,
        v___y_6150_,
        v___y_6151_,
        v___y_6152_,
        v___y_6153_,
        v___y_6154_,
        v___y_6155_,
    );
    lean_dec(v___y_6155_);
    lean_dec_ref(v___y_6154_);
    lean_dec(v___y_6153_);
    lean_dec_ref(v___y_6152_);
    lean_dec(v___y_6151_);
    lean_dec_ref(v___y_6150_);
    lean_dec(v___y_6149_);
    lean_dec_ref(v___y_6148_);
    return v_res_6157_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(
    mut v_a_6158_: *mut LeanObject,
    mut v___y_6159_: *mut LeanObject,
    mut v___y_6160_: *mut LeanObject,
    mut v___y_6161_: *mut LeanObject,
    mut v___y_6162_: *mut LeanObject,
    mut v___y_6163_: *mut LeanObject,
    mut v___y_6164_: *mut LeanObject,
    mut v___y_6165_: *mut LeanObject,
    mut v___y_6166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6178_: u8 = 0;
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6182_: u8 = 0;
    let mut v_a_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6186_: u8 = 0;
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6168_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_6160_,
                    v___y_6163_,
                    v___y_6164_,
                    v___y_6165_,
                    v___y_6166_,
                );
                if lean_obj_tag(v___x_6168_) == 0 {
                    v_a_6169_ = lean_ctor_get(v___x_6168_, 0);
                    lean_inc(v_a_6169_);
                    lean_dec_ref_known(v___x_6168_, 1);
                    v___x_6170_ = l_Lean_Elab_Tactic_Conv_convClear(
                        v_a_6169_,
                        v_a_6158_,
                        v___y_6163_,
                        v___y_6164_,
                        v___y_6165_,
                        v___y_6166_,
                    );
                    if lean_obj_tag(v___x_6170_) == 0 {
                        v_a_6171_ = lean_ctor_get(v___x_6170_, 0);
                        lean_inc(v_a_6171_);
                        lean_dec_ref_known(v___x_6170_, 1);
                        v___x_6172_ = lean_box(0);
                        v___x_6173_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_6173_, 0, v_a_6171_);
                        lean_ctor_set(v___x_6173_, 1, v___x_6172_);
                        v___x_6174_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_6173_,
                            v___y_6160_,
                            v___y_6163_,
                            v___y_6164_,
                            v___y_6165_,
                            v___y_6166_,
                        );
                        return v___x_6174_;
                    } else {
                        v_a_6175_ = lean_ctor_get(v___x_6170_, 0);
                        v_isSharedCheck_6182_ = (!lean_is_exclusive(v___x_6170_)) as u8;
                        if v_isSharedCheck_6182_ == 0 {
                            v___x_6177_ = v___x_6170_;
                            v_isShared_6178_ = v_isSharedCheck_6182_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6175_);
                            lean_dec(v___x_6170_);
                            v___x_6177_ = lean_box(0);
                            v_isShared_6178_ = v_isSharedCheck_6182_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_6158_);
                    v_a_6183_ = lean_ctor_get(v___x_6168_, 0);
                    v_isSharedCheck_6190_ = (!lean_is_exclusive(v___x_6168_)) as u8;
                    if v_isSharedCheck_6190_ == 0 {
                        v___x_6185_ = v___x_6168_;
                        v_isShared_6186_ = v_isSharedCheck_6190_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6183_);
                        lean_dec(v___x_6168_);
                        v___x_6185_ = lean_box(0);
                        v_isShared_6186_ = v_isSharedCheck_6190_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6178_ == 0 {
                    v___x_6180_ = v___x_6177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6181_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_a_6175_);
                    v___x_6180_ = v_reuseFailAlloc_6181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6180_;
            }
            3 => {
                if v_isShared_6186_ == 0 {
                    v___x_6188_ = v___x_6185_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6189_, 0, v_a_6183_);
                    v___x_6188_ = v_reuseFailAlloc_6189_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed(
    mut v_a_6191_: *mut LeanObject,
    mut v___y_6192_: *mut LeanObject,
    mut v___y_6193_: *mut LeanObject,
    mut v___y_6194_: *mut LeanObject,
    mut v___y_6195_: *mut LeanObject,
    mut v___y_6196_: *mut LeanObject,
    mut v___y_6197_: *mut LeanObject,
    mut v___y_6198_: *mut LeanObject,
    mut v___y_6199_: *mut LeanObject,
    mut v___y_6200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6201_: *mut LeanObject = core::ptr::null_mut();
    v_res_6201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(v_a_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_);
    lean_dec(v___y_6199_);
    lean_dec_ref(v___y_6198_);
    lean_dec(v___y_6197_);
    lean_dec_ref(v___y_6196_);
    lean_dec(v___y_6195_);
    lean_dec_ref(v___y_6194_);
    lean_dec(v___y_6193_);
    lean_dec_ref(v___y_6192_);
    return v_res_6201_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(
    mut v_as_6202_: *mut LeanObject,
    mut v_sz_6203_: usize,
    mut v_i_6204_: usize,
    mut v_b_6205_: *mut LeanObject,
    mut v___y_6206_: *mut LeanObject,
    mut v___y_6207_: *mut LeanObject,
    mut v___y_6208_: *mut LeanObject,
    mut v___y_6209_: *mut LeanObject,
    mut v___y_6210_: *mut LeanObject,
    mut v___y_6211_: *mut LeanObject,
    mut v___y_6212_: *mut LeanObject,
    mut v___y_6213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6215_: u8 = 0;
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: usize = 0;
    let mut v___x_6222_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6215_ = lean_usize_dec_lt(v_i_6204_, v_sz_6203_);
                if v___x_6215_ == 0 {
                    v___x_6216_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6216_, 0, v_b_6205_);
                    return v___x_6216_;
                } else {
                    v_a_6217_ = lean_array_uget_borrowed(v_as_6202_, v_i_6204_);
                    lean_inc(v_a_6217_);
                    v___f_6218_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed as *mut core::ffi::c_void, 10, 1);
                    lean_closure_set(v___f_6218_, 0, v_a_6217_);
                    v___x_6219_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v___f_6218_,
                        v___y_6206_,
                        v___y_6207_,
                        v___y_6208_,
                        v___y_6209_,
                        v___y_6210_,
                        v___y_6211_,
                        v___y_6212_,
                        v___y_6213_,
                    );
                    if lean_obj_tag(v___x_6219_) == 0 {
                        lean_dec_ref_known(v___x_6219_, 1);
                        v___x_6220_ = lean_box(0);
                        v___x_6221_ = 1usize;
                        v___x_6222_ = lean_usize_add(v_i_6204_, v___x_6221_);
                        v_i_6204_ = v___x_6222_;
                        v_b_6205_ = v___x_6220_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6219_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___boxed(
    mut v_as_6224_: *mut LeanObject,
    mut v_sz_6225_: *mut LeanObject,
    mut v_i_6226_: *mut LeanObject,
    mut v_b_6227_: *mut LeanObject,
    mut v___y_6228_: *mut LeanObject,
    mut v___y_6229_: *mut LeanObject,
    mut v___y_6230_: *mut LeanObject,
    mut v___y_6231_: *mut LeanObject,
    mut v___y_6232_: *mut LeanObject,
    mut v___y_6233_: *mut LeanObject,
    mut v___y_6234_: *mut LeanObject,
    mut v___y_6235_: *mut LeanObject,
    mut v___y_6236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6237_: usize = 0;
    let mut v_i_boxed_6238_: usize = 0;
    let mut v_res_6239_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6237_ = lean_unbox_usize(v_sz_6225_);
    lean_dec(v_sz_6225_);
    v_i_boxed_6238_ = lean_unbox_usize(v_i_6226_);
    lean_dec(v_i_6226_);
    v_res_6239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(v_as_6224_, v_sz_boxed_6237_, v_i_boxed_6238_, v_b_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_);
    lean_dec(v___y_6235_);
    lean_dec_ref(v___y_6234_);
    lean_dec(v___y_6233_);
    lean_dec_ref(v___y_6232_);
    lean_dec(v___y_6231_);
    lean_dec_ref(v___y_6230_);
    lean_dec(v___y_6229_);
    lean_dec_ref(v___y_6228_);
    lean_dec_ref(v_as_6224_);
    return v_res_6239_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalClear(
    mut v_stx_6247_: *mut LeanObject,
    mut v_a_6248_: *mut LeanObject,
    mut v_a_6249_: *mut LeanObject,
    mut v_a_6250_: *mut LeanObject,
    mut v_a_6251_: *mut LeanObject,
    mut v_a_6252_: *mut LeanObject,
    mut v_a_6253_: *mut LeanObject,
    mut v_a_6254_: *mut LeanObject,
    mut v_a_6255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: u8 = 0;
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hs_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6270_: usize = 0;
    let mut v___x_6271_: usize = 0;
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6275_: u8 = 0;
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6279_: u8 = 0;
    let mut v_unused_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6284_: u8 = 0;
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6288_: u8 = 0;
    let mut v_a_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6292_: u8 = 0;
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6257_ = l_Lean_Elab_Tactic_Conv_evalClear___closed__1;
                lean_inc(v_stx_6247_);
                v___x_6258_ = l_Lean_Syntax_isOfKind(v_stx_6247_, v___x_6257_);
                if v___x_6258_ == 0 {
                    lean_dec(v_stx_6247_);
                    v___x_6259_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
                    return v___x_6259_;
                } else {
                    v___x_6260_ = lean_unsigned_to_nat(1);
                    v___x_6261_ = l_Lean_Syntax_getArg(v_stx_6247_, v___x_6260_);
                    lean_dec(v_stx_6247_);
                    v_hs_6262_ = l_Lean_Syntax_getArgs(v___x_6261_);
                    lean_dec(v___x_6261_);
                    v___x_6263_ = l_Lean_Elab_Tactic_getFVarIds(
                        v_hs_6262_, v_a_6248_, v_a_6249_, v_a_6250_, v_a_6251_, v_a_6252_,
                        v_a_6253_, v_a_6254_, v_a_6255_,
                    );
                    if lean_obj_tag(v___x_6263_) == 0 {
                        v_a_6264_ = lean_ctor_get(v___x_6263_, 0);
                        lean_inc(v_a_6264_);
                        lean_dec_ref_known(v___x_6263_, 1);
                        v___f_6265_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed
                                as *mut core::ffi::c_void,
                            10,
                            1,
                        );
                        lean_closure_set(v___f_6265_, 0, v_a_6264_);
                        v___x_6266_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                            v___f_6265_,
                            v_a_6248_,
                            v_a_6249_,
                            v_a_6250_,
                            v_a_6251_,
                            v_a_6252_,
                            v_a_6253_,
                            v_a_6254_,
                            v_a_6255_,
                        );
                        if lean_obj_tag(v___x_6266_) == 0 {
                            v_a_6267_ = lean_ctor_get(v___x_6266_, 0);
                            lean_inc(v_a_6267_);
                            lean_dec_ref_known(v___x_6266_, 1);
                            v___x_6268_ = l_Array_reverse___redArg(v_a_6267_);
                            v___x_6269_ = lean_box(0);
                            v_sz_6270_ = lean_array_size(v___x_6268_);
                            v___x_6271_ = 0usize;
                            v___x_6272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(v___x_6268_, v_sz_6270_, v___x_6271_, v___x_6269_, v_a_6248_, v_a_6249_, v_a_6250_, v_a_6251_, v_a_6252_, v_a_6253_, v_a_6254_, v_a_6255_);
                            lean_dec_ref(v___x_6268_);
                            if lean_obj_tag(v___x_6272_) == 0 {
                                v_isSharedCheck_6279_ = (!lean_is_exclusive(v___x_6272_)) as u8;
                                if v_isSharedCheck_6279_ == 0 {
                                    v_unused_6280_ = lean_ctor_get(v___x_6272_, 0);
                                    lean_dec(v_unused_6280_);
                                    v___x_6274_ = v___x_6272_;
                                    v_isShared_6275_ = v_isSharedCheck_6279_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_6272_);
                                    v___x_6274_ = lean_box(0);
                                    v_isShared_6275_ = v_isSharedCheck_6279_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                return v___x_6272_;
                            }
                        } else {
                            v_a_6281_ = lean_ctor_get(v___x_6266_, 0);
                            v_isSharedCheck_6288_ = (!lean_is_exclusive(v___x_6266_)) as u8;
                            if v_isSharedCheck_6288_ == 0 {
                                v___x_6283_ = v___x_6266_;
                                v_isShared_6284_ = v_isSharedCheck_6288_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_6281_);
                                lean_dec(v___x_6266_);
                                v___x_6283_ = lean_box(0);
                                v_isShared_6284_ = v_isSharedCheck_6288_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_6289_ = lean_ctor_get(v___x_6263_, 0);
                        v_isSharedCheck_6296_ = (!lean_is_exclusive(v___x_6263_)) as u8;
                        if v_isSharedCheck_6296_ == 0 {
                            v___x_6291_ = v___x_6263_;
                            v_isShared_6292_ = v_isSharedCheck_6296_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_6289_);
                            lean_dec(v___x_6263_);
                            v___x_6291_ = lean_box(0);
                            v_isShared_6292_ = v_isSharedCheck_6296_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6275_ == 0 {
                    lean_ctor_set(v___x_6274_, 0, v___x_6269_);
                    v___x_6277_ = v___x_6274_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6278_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6278_, 0, v___x_6269_);
                    v___x_6277_ = v_reuseFailAlloc_6278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6277_;
            }
            3 => {
                if v_isShared_6284_ == 0 {
                    v___x_6286_ = v___x_6283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6287_, 0, v_a_6281_);
                    v___x_6286_ = v_reuseFailAlloc_6287_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6286_;
            }
            5 => {
                if v_isShared_6292_ == 0 {
                    v___x_6294_ = v___x_6291_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6295_, 0, v_a_6289_);
                    v___x_6294_ = v_reuseFailAlloc_6295_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalClear___boxed(
    mut v_stx_6297_: *mut LeanObject,
    mut v_a_6298_: *mut LeanObject,
    mut v_a_6299_: *mut LeanObject,
    mut v_a_6300_: *mut LeanObject,
    mut v_a_6301_: *mut LeanObject,
    mut v_a_6302_: *mut LeanObject,
    mut v_a_6303_: *mut LeanObject,
    mut v_a_6304_: *mut LeanObject,
    mut v_a_6305_: *mut LeanObject,
    mut v_a_6306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6307_: *mut LeanObject = core::ptr::null_mut();
    v_res_6307_ = l_Lean_Elab_Tactic_Conv_evalClear(
        v_stx_6297_,
        v_a_6298_,
        v_a_6299_,
        v_a_6300_,
        v_a_6301_,
        v_a_6302_,
        v_a_6303_,
        v_a_6304_,
        v_a_6305_,
    );
    lean_dec(v_a_6305_);
    lean_dec_ref(v_a_6304_);
    lean_dec(v_a_6303_);
    lean_dec_ref(v_a_6302_);
    lean_dec(v_a_6301_);
    lean_dec_ref(v_a_6300_);
    lean_dec(v_a_6299_);
    lean_dec_ref(v_a_6298_);
    return v_res_6307_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1()
-> *mut LeanObject {
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    v___x_6316_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_6317_ = l_Lean_Elab_Tactic_Conv_evalClear___closed__1;
    v___x_6318_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1;
    v___x_6319_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalClear___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_6320_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6316_,
        v___x_6317_,
        v___x_6318_,
        v___x_6319_,
    );
    return v___x_6320_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___boxed(
    mut v_a_6321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6322_: *mut LeanObject = core::ptr::null_mut();
    v_res_6322_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
    return v_res_6322_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(
    mut v_as_6323_: *mut LeanObject,
    mut v_sz_6324_: usize,
    mut v_i_6325_: usize,
    mut v_b_6326_: *mut LeanObject,
    mut v___y_6327_: *mut LeanObject,
    mut v___y_6328_: *mut LeanObject,
    mut v___y_6329_: *mut LeanObject,
    mut v___y_6330_: *mut LeanObject,
    mut v___y_6331_: *mut LeanObject,
    mut v___y_6332_: *mut LeanObject,
    mut v___y_6333_: *mut LeanObject,
    mut v___y_6334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: usize = 0;
    let mut v___x_6339_: usize = 0;
    let mut v___x_6341_: u8 = 0;
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_next_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6349_: u8 = 0;
    let mut v___x_6350_: u8 = 0;
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6354_: u8 = 0;
    let mut v_a_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: u8 = 0;
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6370_: u8 = 0;
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6374_: u8 = 0;
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6379_: u8 = 0;
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6383_: u8 = 0;
    let mut v_reuseFailAlloc_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6386_: u8 = 0;
    let mut v_unused_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6341_ = lean_usize_dec_lt(v_i_6325_, v_sz_6324_);
                if v___x_6341_ == 0 {
                    v___x_6342_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6342_, 0, v_b_6326_);
                    return v___x_6342_;
                } else {
                    v_next_6343_ = lean_ctor_get(v_b_6326_, 0);
                    lean_inc(v_next_6343_);
                    if lean_obj_tag(v_next_6343_) == 0 {
                        v___x_6344_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6344_, 0, v_b_6326_);
                        return v___x_6344_;
                    } else {
                        v_upperBound_6345_ = lean_ctor_get(v_b_6326_, 1);
                        v_val_6346_ = lean_ctor_get(v_next_6343_, 0);
                        v_isSharedCheck_6389_ = (!lean_is_exclusive(v_next_6343_)) as u8;
                        if v_isSharedCheck_6389_ == 0 {
                            v___x_6348_ = v_next_6343_;
                            v_isShared_6349_ = v_isSharedCheck_6389_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_6346_);
                            lean_dec(v_next_6343_);
                            v___x_6348_ = lean_box(0);
                            v_isShared_6349_ = v_isSharedCheck_6389_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6338_ = 1usize;
                v___x_6339_ = lean_usize_add(v_i_6325_, v___x_6338_);
                v_i_6325_ = v___x_6339_;
                v_b_6326_ = v_a_6337_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6350_ = lean_nat_dec_lt(v_val_6346_, v_upperBound_6345_);
                if v___x_6350_ == 0 {
                    lean_del_object(v___x_6348_);
                    lean_dec(v_val_6346_);
                    v___x_6351_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6351_, 0, v_b_6326_);
                    return v___x_6351_;
                } else {
                    lean_inc(v_upperBound_6345_);
                    v_isSharedCheck_6386_ = (!lean_is_exclusive(v_b_6326_)) as u8;
                    if v_isSharedCheck_6386_ == 0 {
                        v_unused_6387_ = lean_ctor_get(v_b_6326_, 1);
                        lean_dec(v_unused_6387_);
                        v_unused_6388_ = lean_ctor_get(v_b_6326_, 0);
                        lean_dec(v_unused_6388_);
                        v___x_6353_ = v_b_6326_;
                        v_isShared_6354_ = v_isSharedCheck_6386_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_b_6326_);
                        v___x_6353_ = lean_box(0);
                        v_isShared_6354_ = v_isSharedCheck_6386_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_a_6355_ = lean_array_uget_borrowed(v_as_6323_, v_i_6325_);
                v___x_6356_ = lean_unsigned_to_nat(1);
                v___x_6357_ = lean_nat_add(v_val_6346_, v___x_6356_);
                if v_isShared_6349_ == 0 {
                    lean_ctor_set(v___x_6348_, 0, v___x_6357_);
                    v___x_6359_ = v___x_6348_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6385_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6385_, 0, v___x_6357_);
                    v___x_6359_ = v_reuseFailAlloc_6385_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6354_ == 0 {
                    lean_ctor_set(v___x_6353_, 0, v___x_6359_);
                    v___x_6361_ = v___x_6353_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6384_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6384_, 0, v___x_6359_);
                    lean_ctor_set(v_reuseFailAlloc_6384_, 1, v_upperBound_6345_);
                    v___x_6361_ = v_reuseFailAlloc_6384_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6362_ = lean_unsigned_to_nat(2);
                v___x_6363_ = lean_nat_mod(v_val_6346_, v___x_6362_);
                lean_dec(v_val_6346_);
                v___x_6364_ = lean_unsigned_to_nat(0);
                v___x_6365_ = lean_nat_dec_eq(v___x_6363_, v___x_6364_);
                lean_dec(v___x_6363_);
                if v___x_6365_ == 0 {
                    lean_inc(v_a_6355_);
                    v___x_6366_ = l_Lean_Elab_Tactic_saveTacticInfoForToken(
                        v_a_6355_,
                        v___y_6327_,
                        v___y_6328_,
                        v___y_6329_,
                        v___y_6330_,
                        v___y_6331_,
                        v___y_6332_,
                        v___y_6333_,
                        v___y_6334_,
                    );
                    if lean_obj_tag(v___x_6366_) == 0 {
                        lean_dec_ref_known(v___x_6366_, 1);
                        v_a_6337_ = v___x_6361_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___x_6361_);
                        v_a_6367_ = lean_ctor_get(v___x_6366_, 0);
                        v_isSharedCheck_6374_ = (!lean_is_exclusive(v___x_6366_)) as u8;
                        if v_isSharedCheck_6374_ == 0 {
                            v___x_6369_ = v___x_6366_;
                            v_isShared_6370_ = v_isSharedCheck_6374_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6367_);
                            lean_dec(v___x_6366_);
                            v___x_6369_ = lean_box(0);
                            v_isShared_6370_ = v_isSharedCheck_6374_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_a_6355_);
                    v___x_6375_ = l_Lean_Elab_Tactic_evalTactic(
                        v_a_6355_,
                        v___y_6327_,
                        v___y_6328_,
                        v___y_6329_,
                        v___y_6330_,
                        v___y_6331_,
                        v___y_6332_,
                        v___y_6333_,
                        v___y_6334_,
                    );
                    if lean_obj_tag(v___x_6375_) == 0 {
                        lean_dec_ref_known(v___x_6375_, 1);
                        v_a_6337_ = v___x_6361_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___x_6361_);
                        v_a_6376_ = lean_ctor_get(v___x_6375_, 0);
                        v_isSharedCheck_6383_ = (!lean_is_exclusive(v___x_6375_)) as u8;
                        if v_isSharedCheck_6383_ == 0 {
                            v___x_6378_ = v___x_6375_;
                            v_isShared_6379_ = v_isSharedCheck_6383_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6376_);
                            lean_dec(v___x_6375_);
                            v___x_6378_ = lean_box(0);
                            v_isShared_6379_ = v_isSharedCheck_6383_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            6 => {
                if v_isShared_6370_ == 0 {
                    v___x_6372_ = v___x_6369_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6373_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6373_, 0, v_a_6367_);
                    v___x_6372_ = v_reuseFailAlloc_6373_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6372_;
            }
            8 => {
                if v_isShared_6379_ == 0 {
                    v___x_6381_ = v___x_6378_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6382_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6382_, 0, v_a_6376_);
                    v___x_6381_ = v_reuseFailAlloc_6382_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0___boxed(
    mut v_as_6390_: *mut LeanObject,
    mut v_sz_6391_: *mut LeanObject,
    mut v_i_6392_: *mut LeanObject,
    mut v_b_6393_: *mut LeanObject,
    mut v___y_6394_: *mut LeanObject,
    mut v___y_6395_: *mut LeanObject,
    mut v___y_6396_: *mut LeanObject,
    mut v___y_6397_: *mut LeanObject,
    mut v___y_6398_: *mut LeanObject,
    mut v___y_6399_: *mut LeanObject,
    mut v___y_6400_: *mut LeanObject,
    mut v___y_6401_: *mut LeanObject,
    mut v___y_6402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6403_: usize = 0;
    let mut v_i_boxed_6404_: usize = 0;
    let mut v_res_6405_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6403_ = lean_unbox_usize(v_sz_6391_);
    lean_dec(v_sz_6391_);
    v_i_boxed_6404_ = lean_unbox_usize(v_i_6392_);
    lean_dec(v_i_6392_);
    v_res_6405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(v_as_6390_, v_sz_boxed_6403_, v_i_boxed_6404_, v_b_6393_, v___y_6394_, v___y_6395_, v___y_6396_, v___y_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_);
    lean_dec(v___y_6401_);
    lean_dec_ref(v___y_6400_);
    lean_dec(v___y_6399_);
    lean_dec_ref(v___y_6398_);
    lean_dec(v___y_6397_);
    lean_dec_ref(v___y_6396_);
    lean_dec(v___y_6395_);
    lean_dec_ref(v___y_6394_);
    lean_dec_ref(v_as_6390_);
    return v_res_6405_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(
    mut v_stx_6408_: *mut LeanObject,
    mut v_a_6409_: *mut LeanObject,
    mut v_a_6410_: *mut LeanObject,
    mut v_a_6411_: *mut LeanObject,
    mut v_a_6412_: *mut LeanObject,
    mut v_a_6413_: *mut LeanObject,
    mut v_a_6414_: *mut LeanObject,
    mut v_a_6415_: *mut LeanObject,
    mut v_a_6416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6422_: usize = 0;
    let mut v___x_6423_: usize = 0;
    let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6427_: u8 = 0;
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6432_: u8 = 0;
    let mut v_unused_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6437_: u8 = 0;
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6418_ = l_Lean_Syntax_getArgs(v_stx_6408_);
                v___x_6419_ = lean_array_get_size(v___x_6418_);
                v___x_6420_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0;
                v___x_6421_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6421_, 0, v___x_6420_);
                lean_ctor_set(v___x_6421_, 1, v___x_6419_);
                v_sz_6422_ = lean_array_size(v___x_6418_);
                v___x_6423_ = 0usize;
                v___x_6424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(v___x_6418_, v_sz_6422_, v___x_6423_, v___x_6421_, v_a_6409_, v_a_6410_, v_a_6411_, v_a_6412_, v_a_6413_, v_a_6414_, v_a_6415_, v_a_6416_);
                lean_dec_ref(v___x_6418_);
                if lean_obj_tag(v___x_6424_) == 0 {
                    v_isSharedCheck_6432_ = (!lean_is_exclusive(v___x_6424_)) as u8;
                    if v_isSharedCheck_6432_ == 0 {
                        v_unused_6433_ = lean_ctor_get(v___x_6424_, 0);
                        lean_dec(v_unused_6433_);
                        v___x_6426_ = v___x_6424_;
                        v_isShared_6427_ = v_isSharedCheck_6432_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_6424_);
                        v___x_6426_ = lean_box(0);
                        v_isShared_6427_ = v_isSharedCheck_6432_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6434_ = lean_ctor_get(v___x_6424_, 0);
                    v_isSharedCheck_6441_ = (!lean_is_exclusive(v___x_6424_)) as u8;
                    if v_isSharedCheck_6441_ == 0 {
                        v___x_6436_ = v___x_6424_;
                        v_isShared_6437_ = v_isSharedCheck_6441_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6434_);
                        lean_dec(v___x_6424_);
                        v___x_6436_ = lean_box(0);
                        v_isShared_6437_ = v_isSharedCheck_6441_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6428_ = lean_box(0);
                if v_isShared_6427_ == 0 {
                    lean_ctor_set(v___x_6426_, 0, v___x_6428_);
                    v___x_6430_ = v___x_6426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6431_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6431_, 0, v___x_6428_);
                    v___x_6430_ = v_reuseFailAlloc_6431_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6430_;
            }
            3 => {
                if v_isShared_6437_ == 0 {
                    v___x_6439_ = v___x_6436_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6440_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6440_, 0, v_a_6434_);
                    v___x_6439_ = v_reuseFailAlloc_6440_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___boxed(
    mut v_stx_6442_: *mut LeanObject,
    mut v_a_6443_: *mut LeanObject,
    mut v_a_6444_: *mut LeanObject,
    mut v_a_6445_: *mut LeanObject,
    mut v_a_6446_: *mut LeanObject,
    mut v_a_6447_: *mut LeanObject,
    mut v_a_6448_: *mut LeanObject,
    mut v_a_6449_: *mut LeanObject,
    mut v_a_6450_: *mut LeanObject,
    mut v_a_6451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6452_: *mut LeanObject = core::ptr::null_mut();
    v_res_6452_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(
        v_stx_6442_,
        v_a_6443_,
        v_a_6444_,
        v_a_6445_,
        v_a_6446_,
        v_a_6447_,
        v_a_6448_,
        v_a_6449_,
        v_a_6450_,
    );
    lean_dec(v_a_6450_);
    lean_dec_ref(v_a_6449_);
    lean_dec(v_a_6448_);
    lean_dec_ref(v_a_6447_);
    lean_dec(v_a_6446_);
    lean_dec_ref(v_a_6445_);
    lean_dec(v_a_6444_);
    lean_dec_ref(v_a_6443_);
    lean_dec(v_stx_6442_);
    return v_res_6452_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(
    mut v_stx_6453_: *mut LeanObject,
    mut v_a_6454_: *mut LeanObject,
    mut v_a_6455_: *mut LeanObject,
    mut v_a_6456_: *mut LeanObject,
    mut v_a_6457_: *mut LeanObject,
    mut v_a_6458_: *mut LeanObject,
    mut v_a_6459_: *mut LeanObject,
    mut v_a_6460_: *mut LeanObject,
    mut v_a_6461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut LeanObject = core::ptr::null_mut();
    v___x_6463_ = lean_unsigned_to_nat(0);
    v___x_6464_ = l_Lean_Syntax_getArg(v_stx_6453_, v___x_6463_);
    v___x_6465_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(
        v___x_6464_,
        v_a_6454_,
        v_a_6455_,
        v_a_6456_,
        v_a_6457_,
        v_a_6458_,
        v_a_6459_,
        v_a_6460_,
        v_a_6461_,
    );
    lean_dec(v___x_6464_);
    return v___x_6465_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed(
    mut v_stx_6466_: *mut LeanObject,
    mut v_a_6467_: *mut LeanObject,
    mut v_a_6468_: *mut LeanObject,
    mut v_a_6469_: *mut LeanObject,
    mut v_a_6470_: *mut LeanObject,
    mut v_a_6471_: *mut LeanObject,
    mut v_a_6472_: *mut LeanObject,
    mut v_a_6473_: *mut LeanObject,
    mut v_a_6474_: *mut LeanObject,
    mut v_a_6475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6476_: *mut LeanObject = core::ptr::null_mut();
    v_res_6476_ = l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(
        v_stx_6466_,
        v_a_6467_,
        v_a_6468_,
        v_a_6469_,
        v_a_6470_,
        v_a_6471_,
        v_a_6472_,
        v_a_6473_,
        v_a_6474_,
    );
    lean_dec(v_a_6474_);
    lean_dec_ref(v_a_6473_);
    lean_dec(v_a_6472_);
    lean_dec_ref(v_a_6471_);
    lean_dec(v_a_6470_);
    lean_dec_ref(v_a_6469_);
    lean_dec(v_a_6468_);
    lean_dec_ref(v_a_6467_);
    lean_dec(v_stx_6466_);
    return v_res_6476_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1()
-> *mut LeanObject {
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    v___x_6492_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_6493_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1;
    v___x_6494_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3;
    v___x_6495_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_6496_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6492_,
        v___x_6493_,
        v___x_6494_,
        v___x_6495_,
    );
    return v___x_6496_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___boxed(
    mut v_a_6497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6498_: *mut LeanObject = core::ptr::null_mut();
    v_res_6498_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
    return v_res_6498_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3()
-> *mut LeanObject {
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    v___x_6525_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3;
    v___x_6526_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6;
    v___x_6527_ = l_Lean_addBuiltinDeclarationRanges(v___x_6525_, v___x_6526_);
    return v___x_6527_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___boxed(
    mut v_a_6528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6529_: *mut LeanObject = core::ptr::null_mut();
    v_res_6529_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
    return v_res_6529_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(
    mut v_a_6530_: *mut LeanObject,
    mut v_trees_6531_: *mut LeanObject,
    mut v___y_6532_: *mut LeanObject,
    mut v___y_6533_: *mut LeanObject,
    mut v___y_6534_: *mut LeanObject,
    mut v___y_6535_: *mut LeanObject,
    mut v___y_6536_: *mut LeanObject,
    mut v___y_6537_: *mut LeanObject,
    mut v___y_6538_: *mut LeanObject,
    mut v___y_6539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6545_: u8 = 0;
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6550_: u8 = 0;
    let mut v_a_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6554_: u8 = 0;
    let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_6539_);
                lean_inc_ref(v___y_6538_);
                lean_inc(v___y_6537_);
                lean_inc_ref(v___y_6536_);
                lean_inc(v___y_6535_);
                lean_inc_ref(v___y_6534_);
                lean_inc(v___y_6533_);
                lean_inc_ref(v___y_6532_);
                v___x_6541_ = lean_apply_9(
                    v_a_6530_,
                    v___y_6532_,
                    v___y_6533_,
                    v___y_6534_,
                    v___y_6535_,
                    v___y_6536_,
                    v___y_6537_,
                    v___y_6538_,
                    v___y_6539_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6541_) == 0 {
                    v_a_6542_ = lean_ctor_get(v___x_6541_, 0);
                    v_isSharedCheck_6550_ = (!lean_is_exclusive(v___x_6541_)) as u8;
                    if v_isSharedCheck_6550_ == 0 {
                        v___x_6544_ = v___x_6541_;
                        v_isShared_6545_ = v_isSharedCheck_6550_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6542_);
                        lean_dec(v___x_6541_);
                        v___x_6544_ = lean_box(0);
                        v_isShared_6545_ = v_isSharedCheck_6550_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_trees_6531_);
                    v_a_6551_ = lean_ctor_get(v___x_6541_, 0);
                    v_isSharedCheck_6558_ = (!lean_is_exclusive(v___x_6541_)) as u8;
                    if v_isSharedCheck_6558_ == 0 {
                        v___x_6553_ = v___x_6541_;
                        v_isShared_6554_ = v_isSharedCheck_6558_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6551_);
                        lean_dec(v___x_6541_);
                        v___x_6553_ = lean_box(0);
                        v_isShared_6554_ = v_isSharedCheck_6558_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6546_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6546_, 0, v_a_6542_);
                lean_ctor_set(v___x_6546_, 1, v_trees_6531_);
                if v_isShared_6545_ == 0 {
                    lean_ctor_set(v___x_6544_, 0, v___x_6546_);
                    v___x_6548_ = v___x_6544_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6549_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6549_, 0, v___x_6546_);
                    v___x_6548_ = v_reuseFailAlloc_6549_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6548_;
            }
            3 => {
                if v_isShared_6554_ == 0 {
                    v___x_6556_ = v___x_6553_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6557_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6557_, 0, v_a_6551_);
                    v___x_6556_ = v_reuseFailAlloc_6557_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed(
    mut v_a_6559_: *mut LeanObject,
    mut v_trees_6560_: *mut LeanObject,
    mut v___y_6561_: *mut LeanObject,
    mut v___y_6562_: *mut LeanObject,
    mut v___y_6563_: *mut LeanObject,
    mut v___y_6564_: *mut LeanObject,
    mut v___y_6565_: *mut LeanObject,
    mut v___y_6566_: *mut LeanObject,
    mut v___y_6567_: *mut LeanObject,
    mut v___y_6568_: *mut LeanObject,
    mut v___y_6569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6570_: *mut LeanObject = core::ptr::null_mut();
    v_res_6570_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(
        v_a_6559_,
        v_trees_6560_,
        v___y_6561_,
        v___y_6562_,
        v___y_6563_,
        v___y_6564_,
        v___y_6565_,
        v___y_6566_,
        v___y_6567_,
        v___y_6568_,
    );
    lean_dec(v___y_6568_);
    lean_dec_ref(v___y_6567_);
    lean_dec(v___y_6566_);
    lean_dec_ref(v___y_6565_);
    lean_dec(v___y_6564_);
    lean_dec_ref(v___y_6563_);
    lean_dec(v___y_6562_);
    lean_dec_ref(v___y_6561_);
    return v_res_6570_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(
    mut v___x_6571_: *mut LeanObject,
    mut v___y_6572_: *mut LeanObject,
    mut v___y_6573_: *mut LeanObject,
    mut v___y_6574_: *mut LeanObject,
    mut v___y_6575_: *mut LeanObject,
    mut v___y_6576_: *mut LeanObject,
    mut v___y_6577_: *mut LeanObject,
    mut v___y_6578_: *mut LeanObject,
    mut v___y_6579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    v___x_6581_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6581_, 0, v___x_6571_);
    return v___x_6581_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1___boxed(
    mut v___x_6582_: *mut LeanObject,
    mut v___y_6583_: *mut LeanObject,
    mut v___y_6584_: *mut LeanObject,
    mut v___y_6585_: *mut LeanObject,
    mut v___y_6586_: *mut LeanObject,
    mut v___y_6587_: *mut LeanObject,
    mut v___y_6588_: *mut LeanObject,
    mut v___y_6589_: *mut LeanObject,
    mut v___y_6590_: *mut LeanObject,
    mut v___y_6591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6592_: *mut LeanObject = core::ptr::null_mut();
    v_res_6592_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(
        v___x_6582_,
        v___y_6583_,
        v___y_6584_,
        v___y_6585_,
        v___y_6586_,
        v___y_6587_,
        v___y_6588_,
        v___y_6589_,
        v___y_6590_,
    );
    lean_dec(v___y_6590_);
    lean_dec_ref(v___y_6589_);
    lean_dec(v___y_6588_);
    lean_dec_ref(v___y_6587_);
    lean_dec(v___y_6586_);
    lean_dec_ref(v___y_6585_);
    lean_dec(v___y_6584_);
    lean_dec_ref(v___y_6583_);
    return v_res_6592_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(
    mut v___y_6593_: *mut LeanObject,
    mut v_mkInfoTree_6594_: *mut LeanObject,
    mut v___y_6595_: *mut LeanObject,
    mut v___y_6596_: *mut LeanObject,
    mut v___y_6597_: *mut LeanObject,
    mut v___y_6598_: *mut LeanObject,
    mut v___y_6599_: *mut LeanObject,
    mut v___y_6600_: *mut LeanObject,
    mut v___y_6601_: *mut LeanObject,
    mut v_a_6602_: *mut LeanObject,
    mut v_a_x3f_6603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6612_: u8 = 0;
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6625_: u8 = 0;
    let mut v_enabled_6626_: u8 = 0;
    let mut v_assignment_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6631_: u8 = 0;
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6644_: u8 = 0;
    let mut v_unused_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6646_: u8 = 0;
    let mut v_isSharedCheck_6647_: u8 = 0;
    let mut v_a_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6605_ = lean_st_ref_get(v___y_6593_);
                v_infoState_6606_ = lean_ctor_get(v___x_6605_, 7);
                lean_inc_ref(v_infoState_6606_);
                lean_dec(v___x_6605_);
                v_trees_6607_ = lean_ctor_get(v_infoState_6606_, 2);
                lean_inc_ref(v_trees_6607_);
                lean_dec_ref(v_infoState_6606_);
                lean_inc(v___y_6593_);
                lean_inc_ref(v___y_6601_);
                lean_inc(v___y_6600_);
                lean_inc_ref(v___y_6599_);
                lean_inc(v___y_6598_);
                lean_inc_ref(v___y_6597_);
                lean_inc(v___y_6596_);
                lean_inc_ref(v___y_6595_);
                v___x_6608_ = lean_apply_10(
                    v_mkInfoTree_6594_,
                    v_trees_6607_,
                    v___y_6595_,
                    v___y_6596_,
                    v___y_6597_,
                    v___y_6598_,
                    v___y_6599_,
                    v___y_6600_,
                    v___y_6601_,
                    v___y_6593_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6608_) == 0 {
                    v_a_6609_ = lean_ctor_get(v___x_6608_, 0);
                    v_isSharedCheck_6647_ = (!lean_is_exclusive(v___x_6608_)) as u8;
                    if v_isSharedCheck_6647_ == 0 {
                        v___x_6611_ = v___x_6608_;
                        v_isShared_6612_ = v_isSharedCheck_6647_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6609_);
                        lean_dec(v___x_6608_);
                        v___x_6611_ = lean_box(0);
                        v_isShared_6612_ = v_isSharedCheck_6647_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_6602_);
                    v_a_6648_ = lean_ctor_get(v___x_6608_, 0);
                    v_isSharedCheck_6655_ = (!lean_is_exclusive(v___x_6608_)) as u8;
                    if v_isSharedCheck_6655_ == 0 {
                        v___x_6650_ = v___x_6608_;
                        v_isShared_6651_ = v_isSharedCheck_6655_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_6648_);
                        lean_dec(v___x_6608_);
                        v___x_6650_ = lean_box(0);
                        v_isShared_6651_ = v_isSharedCheck_6655_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6613_ = lean_st_ref_take(v___y_6593_);
                v_infoState_6614_ = lean_ctor_get(v___x_6613_, 7);
                v_env_6615_ = lean_ctor_get(v___x_6613_, 0);
                v_nextMacroScope_6616_ = lean_ctor_get(v___x_6613_, 1);
                v_ngen_6617_ = lean_ctor_get(v___x_6613_, 2);
                v_auxDeclNGen_6618_ = lean_ctor_get(v___x_6613_, 3);
                v_traceState_6619_ = lean_ctor_get(v___x_6613_, 4);
                v_cache_6620_ = lean_ctor_get(v___x_6613_, 5);
                v_messages_6621_ = lean_ctor_get(v___x_6613_, 6);
                v_snapshotTasks_6622_ = lean_ctor_get(v___x_6613_, 8);
                v_isSharedCheck_6646_ = (!lean_is_exclusive(v___x_6613_)) as u8;
                if v_isSharedCheck_6646_ == 0 {
                    v___x_6624_ = v___x_6613_;
                    v_isShared_6625_ = v_isSharedCheck_6646_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6622_);
                    lean_inc(v_infoState_6614_);
                    lean_inc(v_messages_6621_);
                    lean_inc(v_cache_6620_);
                    lean_inc(v_traceState_6619_);
                    lean_inc(v_auxDeclNGen_6618_);
                    lean_inc(v_ngen_6617_);
                    lean_inc(v_nextMacroScope_6616_);
                    lean_inc(v_env_6615_);
                    lean_dec(v___x_6613_);
                    v___x_6624_ = lean_box(0);
                    v_isShared_6625_ = v_isSharedCheck_6646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_6626_ = lean_ctor_get_uint8(
                    v_infoState_6614_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_6627_ = lean_ctor_get(v_infoState_6614_, 0);
                v_lazyAssignment_6628_ = lean_ctor_get(v_infoState_6614_, 1);
                v_isSharedCheck_6644_ = (!lean_is_exclusive(v_infoState_6614_)) as u8;
                if v_isSharedCheck_6644_ == 0 {
                    v_unused_6645_ = lean_ctor_get(v_infoState_6614_, 2);
                    lean_dec(v_unused_6645_);
                    v___x_6630_ = v_infoState_6614_;
                    v_isShared_6631_ = v_isSharedCheck_6644_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_6628_);
                    lean_inc(v_assignment_6627_);
                    lean_dec(v_infoState_6614_);
                    v___x_6630_ = lean_box(0);
                    v_isShared_6631_ = v_isSharedCheck_6644_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6632_ = l_Lean_PersistentArray_push___redArg(v_a_6602_, v_a_6609_);
                if v_isShared_6631_ == 0 {
                    lean_ctor_set(v___x_6630_, 2, v___x_6632_);
                    v___x_6634_ = v___x_6630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6643_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6643_, 0, v_assignment_6627_);
                    lean_ctor_set(v_reuseFailAlloc_6643_, 1, v_lazyAssignment_6628_);
                    lean_ctor_set(v_reuseFailAlloc_6643_, 2, v___x_6632_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6643_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_6626_,
                    );
                    v___x_6634_ = v_reuseFailAlloc_6643_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6625_ == 0 {
                    lean_ctor_set(v___x_6624_, 7, v___x_6634_);
                    v___x_6636_ = v___x_6624_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6642_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6642_, 0, v_env_6615_);
                    lean_ctor_set(v_reuseFailAlloc_6642_, 1, v_nextMacroScope_6616_);
                    lean_ctor_set(v_reuseFailAlloc_6642_, 2, v_ngen_6617_);
                    lean_ctor_set(v_reuseFailAlloc_6642_, 3, v_auxDeclNGen_6618_);
                    lean_ctor_set(v_reuseFailAlloc_6642_, 4, v_traceState_6619_);
                    lean_ctor_set(v_reuseFailAlloc_6642_, 5, v_cache_6620_);
                    lean_ctor_set(v_reuseFailAlloc_6642_, 6, v_messages_6621_);
                    lean_ctor_set(v_reuseFailAlloc_6642_, 7, v___x_6634_);
                    lean_ctor_set(v_reuseFailAlloc_6642_, 8, v_snapshotTasks_6622_);
                    v___x_6636_ = v_reuseFailAlloc_6642_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6637_ = lean_st_ref_set(v___y_6593_, v___x_6636_);
                v___x_6638_ = lean_box(0);
                if v_isShared_6612_ == 0 {
                    lean_ctor_set(v___x_6611_, 0, v___x_6638_);
                    v___x_6640_ = v___x_6611_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6641_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6641_, 0, v___x_6638_);
                    v___x_6640_ = v_reuseFailAlloc_6641_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6640_;
            }
            7 => {
                if v_isShared_6651_ == 0 {
                    v___x_6653_ = v___x_6650_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6654_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6654_, 0, v_a_6648_);
                    v___x_6653_ = v_reuseFailAlloc_6654_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0___boxed(
    mut v___y_6656_: *mut LeanObject,
    mut v_mkInfoTree_6657_: *mut LeanObject,
    mut v___y_6658_: *mut LeanObject,
    mut v___y_6659_: *mut LeanObject,
    mut v___y_6660_: *mut LeanObject,
    mut v___y_6661_: *mut LeanObject,
    mut v___y_6662_: *mut LeanObject,
    mut v___y_6663_: *mut LeanObject,
    mut v___y_6664_: *mut LeanObject,
    mut v_a_6665_: *mut LeanObject,
    mut v_a_x3f_6666_: *mut LeanObject,
    mut v___y_6667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6668_: *mut LeanObject = core::ptr::null_mut();
    v_res_6668_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_6656_, v_mkInfoTree_6657_, v___y_6658_, v___y_6659_, v___y_6660_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_, v_a_6665_, v_a_x3f_6666_);
    lean_dec(v_a_x3f_6666_);
    lean_dec_ref(v___y_6664_);
    lean_dec(v___y_6663_);
    lean_dec_ref(v___y_6662_);
    lean_dec(v___y_6661_);
    lean_dec_ref(v___y_6660_);
    lean_dec(v___y_6659_);
    lean_dec_ref(v___y_6658_);
    lean_dec(v___y_6656_);
    return v_res_6668_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    v___x_6669_ = lean_unsigned_to_nat(32);
    v___x_6670_ = lean_mk_empty_array_with_capacity(v___x_6669_);
    v___x_6671_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6671_, 0, v___x_6670_);
    return v___x_6671_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_6672_: usize = 0;
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    v___x_6672_ = 5usize;
    v___x_6673_ = lean_unsigned_to_nat(0);
    v___x_6674_ = lean_unsigned_to_nat(32);
    v___x_6675_ = lean_mk_empty_array_with_capacity(v___x_6674_);
    v___x_6676_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0);
    v___x_6677_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_6677_, 0, v___x_6676_);
    lean_ctor_set(v___x_6677_, 1, v___x_6675_);
    lean_ctor_set(v___x_6677_, 2, v___x_6673_);
    lean_ctor_set(v___x_6677_, 3, v___x_6673_);
    lean_ctor_set_usize(v___x_6677_, 4, v___x_6672_);
    return v___x_6677_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(
    mut v___y_6678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6695_: u8 = 0;
    let mut v_enabled_6696_: u8 = 0;
    let mut v_assignment_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6701_: u8 = 0;
    let mut v___x_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6711_: u8 = 0;
    let mut v_unused_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6680_ = lean_st_ref_get(v___y_6678_);
                v_infoState_6681_ = lean_ctor_get(v___x_6680_, 7);
                lean_inc_ref(v_infoState_6681_);
                lean_dec(v___x_6680_);
                v_trees_6682_ = lean_ctor_get(v_infoState_6681_, 2);
                lean_inc_ref(v_trees_6682_);
                lean_dec_ref(v_infoState_6681_);
                v___x_6683_ = lean_st_ref_take(v___y_6678_);
                v_infoState_6684_ = lean_ctor_get(v___x_6683_, 7);
                v_env_6685_ = lean_ctor_get(v___x_6683_, 0);
                v_nextMacroScope_6686_ = lean_ctor_get(v___x_6683_, 1);
                v_ngen_6687_ = lean_ctor_get(v___x_6683_, 2);
                v_auxDeclNGen_6688_ = lean_ctor_get(v___x_6683_, 3);
                v_traceState_6689_ = lean_ctor_get(v___x_6683_, 4);
                v_cache_6690_ = lean_ctor_get(v___x_6683_, 5);
                v_messages_6691_ = lean_ctor_get(v___x_6683_, 6);
                v_snapshotTasks_6692_ = lean_ctor_get(v___x_6683_, 8);
                v_isSharedCheck_6713_ = (!lean_is_exclusive(v___x_6683_)) as u8;
                if v_isSharedCheck_6713_ == 0 {
                    v___x_6694_ = v___x_6683_;
                    v_isShared_6695_ = v_isSharedCheck_6713_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6692_);
                    lean_inc(v_infoState_6684_);
                    lean_inc(v_messages_6691_);
                    lean_inc(v_cache_6690_);
                    lean_inc(v_traceState_6689_);
                    lean_inc(v_auxDeclNGen_6688_);
                    lean_inc(v_ngen_6687_);
                    lean_inc(v_nextMacroScope_6686_);
                    lean_inc(v_env_6685_);
                    lean_dec(v___x_6683_);
                    v___x_6694_ = lean_box(0);
                    v_isShared_6695_ = v_isSharedCheck_6713_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_6696_ = lean_ctor_get_uint8(
                    v_infoState_6684_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_6697_ = lean_ctor_get(v_infoState_6684_, 0);
                v_lazyAssignment_6698_ = lean_ctor_get(v_infoState_6684_, 1);
                v_isSharedCheck_6711_ = (!lean_is_exclusive(v_infoState_6684_)) as u8;
                if v_isSharedCheck_6711_ == 0 {
                    v_unused_6712_ = lean_ctor_get(v_infoState_6684_, 2);
                    lean_dec(v_unused_6712_);
                    v___x_6700_ = v_infoState_6684_;
                    v_isShared_6701_ = v_isSharedCheck_6711_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_6698_);
                    lean_inc(v_assignment_6697_);
                    lean_dec(v_infoState_6684_);
                    v___x_6700_ = lean_box(0);
                    v_isShared_6701_ = v_isSharedCheck_6711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6702_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1);
                if v_isShared_6701_ == 0 {
                    lean_ctor_set(v___x_6700_, 2, v___x_6702_);
                    v___x_6704_ = v___x_6700_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6710_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6710_, 0, v_assignment_6697_);
                    lean_ctor_set(v_reuseFailAlloc_6710_, 1, v_lazyAssignment_6698_);
                    lean_ctor_set(v_reuseFailAlloc_6710_, 2, v___x_6702_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6710_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_6696_,
                    );
                    v___x_6704_ = v_reuseFailAlloc_6710_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6695_ == 0 {
                    lean_ctor_set(v___x_6694_, 7, v___x_6704_);
                    v___x_6706_ = v___x_6694_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6709_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 0, v_env_6685_);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 1, v_nextMacroScope_6686_);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 2, v_ngen_6687_);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 3, v_auxDeclNGen_6688_);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 4, v_traceState_6689_);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 5, v_cache_6690_);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 6, v_messages_6691_);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 7, v___x_6704_);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 8, v_snapshotTasks_6692_);
                    v___x_6706_ = v_reuseFailAlloc_6709_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6707_ = lean_st_ref_set(v___y_6678_, v___x_6706_);
                v___x_6708_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6708_, 0, v_trees_6682_);
                return v___x_6708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___boxed(
    mut v___y_6714_: *mut LeanObject,
    mut v___y_6715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6716_: *mut LeanObject = core::ptr::null_mut();
    v_res_6716_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_6714_);
    lean_dec(v___y_6714_);
    return v_res_6716_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(
    mut v_x_6717_: *mut LeanObject,
    mut v_mkInfoTree_6718_: *mut LeanObject,
    mut v___y_6719_: *mut LeanObject,
    mut v___y_6720_: *mut LeanObject,
    mut v___y_6721_: *mut LeanObject,
    mut v___y_6722_: *mut LeanObject,
    mut v___y_6723_: *mut LeanObject,
    mut v___y_6724_: *mut LeanObject,
    mut v___y_6725_: *mut LeanObject,
    mut v___y_6726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_6730_: u8 = 0;
    let mut v___x_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6738_: u8 = 0;
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6744_: u8 = 0;
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6748_: u8 = 0;
    let mut v_unused_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6753_: u8 = 0;
    let mut v___x_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6757_: u8 = 0;
    let mut v_reuseFailAlloc_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6759_: u8 = 0;
    let mut v_a_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6765_: u8 = 0;
    let mut v___x_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6769_: u8 = 0;
    let mut v_unused_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6774_: u8 = 0;
    let mut v___x_6776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6728_ = lean_st_ref_get(v___y_6726_);
                v_infoState_6729_ = lean_ctor_get(v___x_6728_, 7);
                lean_inc_ref(v_infoState_6729_);
                lean_dec(v___x_6728_);
                v_enabled_6730_ = lean_ctor_get_uint8(
                    v_infoState_6729_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_6729_);
                if v_enabled_6730_ == 0 {
                    lean_dec_ref(v_mkInfoTree_6718_);
                    lean_inc(v___y_6726_);
                    lean_inc_ref(v___y_6725_);
                    lean_inc(v___y_6724_);
                    lean_inc_ref(v___y_6723_);
                    lean_inc(v___y_6722_);
                    lean_inc_ref(v___y_6721_);
                    lean_inc(v___y_6720_);
                    lean_inc_ref(v___y_6719_);
                    v___x_6731_ = lean_apply_9(
                        v_x_6717_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        v___y_6724_,
                        v___y_6725_,
                        v___y_6726_,
                        lean_box(0),
                    );
                    return v___x_6731_;
                } else {
                    v___x_6732_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_6726_);
                    v_a_6733_ = lean_ctor_get(v___x_6732_, 0);
                    lean_inc(v_a_6733_);
                    lean_dec_ref(v___x_6732_);
                    lean_inc(v___y_6726_);
                    lean_inc_ref(v___y_6725_);
                    lean_inc(v___y_6724_);
                    lean_inc_ref(v___y_6723_);
                    lean_inc(v___y_6722_);
                    lean_inc_ref(v___y_6721_);
                    lean_inc(v___y_6720_);
                    lean_inc_ref(v___y_6719_);
                    v_r_6734_ = lean_apply_9(
                        v_x_6717_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        v___y_6724_,
                        v___y_6725_,
                        v___y_6726_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_6734_) == 0 {
                        v_a_6735_ = lean_ctor_get(v_r_6734_, 0);
                        v_isSharedCheck_6759_ = (!lean_is_exclusive(v_r_6734_)) as u8;
                        if v_isSharedCheck_6759_ == 0 {
                            v___x_6737_ = v_r_6734_;
                            v_isShared_6738_ = v_isSharedCheck_6759_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6735_);
                            lean_dec(v_r_6734_);
                            v___x_6737_ = lean_box(0);
                            v_isShared_6738_ = v_isSharedCheck_6759_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6760_ = lean_ctor_get(v_r_6734_, 0);
                        lean_inc(v_a_6760_);
                        lean_dec_ref_known(v_r_6734_, 1);
                        v___x_6761_ = lean_box(0);
                        v___x_6762_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_6726_, v_mkInfoTree_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_, v___y_6724_, v___y_6725_, v_a_6733_, v___x_6761_);
                        if lean_obj_tag(v___x_6762_) == 0 {
                            v_isSharedCheck_6769_ = (!lean_is_exclusive(v___x_6762_)) as u8;
                            if v_isSharedCheck_6769_ == 0 {
                                v_unused_6770_ = lean_ctor_get(v___x_6762_, 0);
                                lean_dec(v_unused_6770_);
                                v___x_6764_ = v___x_6762_;
                                v_isShared_6765_ = v_isSharedCheck_6769_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_6762_);
                                v___x_6764_ = lean_box(0);
                                v_isShared_6765_ = v_isSharedCheck_6769_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_6760_);
                            v_a_6771_ = lean_ctor_get(v___x_6762_, 0);
                            v_isSharedCheck_6778_ = (!lean_is_exclusive(v___x_6762_)) as u8;
                            if v_isSharedCheck_6778_ == 0 {
                                v___x_6773_ = v___x_6762_;
                                v_isShared_6774_ = v_isSharedCheck_6778_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_6771_);
                                lean_dec(v___x_6762_);
                                v___x_6773_ = lean_box(0);
                                v_isShared_6774_ = v_isSharedCheck_6778_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_6735_);
                if v_isShared_6738_ == 0 {
                    lean_ctor_set_tag(v___x_6737_, 1);
                    v___x_6740_ = v___x_6737_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6758_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6758_, 0, v_a_6735_);
                    v___x_6740_ = v_reuseFailAlloc_6758_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6741_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_6726_, v_mkInfoTree_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_, v___y_6724_, v___y_6725_, v_a_6733_, v___x_6740_);
                lean_dec_ref(v___x_6740_);
                if lean_obj_tag(v___x_6741_) == 0 {
                    v_isSharedCheck_6748_ = (!lean_is_exclusive(v___x_6741_)) as u8;
                    if v_isSharedCheck_6748_ == 0 {
                        v_unused_6749_ = lean_ctor_get(v___x_6741_, 0);
                        lean_dec(v_unused_6749_);
                        v___x_6743_ = v___x_6741_;
                        v_isShared_6744_ = v_isSharedCheck_6748_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_6741_);
                        v___x_6743_ = lean_box(0);
                        v_isShared_6744_ = v_isSharedCheck_6748_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6735_);
                    v_a_6750_ = lean_ctor_get(v___x_6741_, 0);
                    v_isSharedCheck_6757_ = (!lean_is_exclusive(v___x_6741_)) as u8;
                    if v_isSharedCheck_6757_ == 0 {
                        v___x_6752_ = v___x_6741_;
                        v_isShared_6753_ = v_isSharedCheck_6757_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6750_);
                        lean_dec(v___x_6741_);
                        v___x_6752_ = lean_box(0);
                        v_isShared_6753_ = v_isSharedCheck_6757_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6744_ == 0 {
                    lean_ctor_set(v___x_6743_, 0, v_a_6735_);
                    v___x_6746_ = v___x_6743_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6747_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6747_, 0, v_a_6735_);
                    v___x_6746_ = v_reuseFailAlloc_6747_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6746_;
            }
            5 => {
                if v_isShared_6753_ == 0 {
                    v___x_6755_ = v___x_6752_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6756_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6756_, 0, v_a_6750_);
                    v___x_6755_ = v_reuseFailAlloc_6756_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6755_;
            }
            7 => {
                if v_isShared_6765_ == 0 {
                    lean_ctor_set_tag(v___x_6764_, 1);
                    lean_ctor_set(v___x_6764_, 0, v_a_6760_);
                    v___x_6767_ = v___x_6764_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6768_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6768_, 0, v_a_6760_);
                    v___x_6767_ = v_reuseFailAlloc_6768_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6767_;
            }
            9 => {
                if v_isShared_6774_ == 0 {
                    v___x_6776_ = v___x_6773_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6777_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6777_, 0, v_a_6771_);
                    v___x_6776_ = v_reuseFailAlloc_6777_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6776_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___boxed(
    mut v_x_6779_: *mut LeanObject,
    mut v_mkInfoTree_6780_: *mut LeanObject,
    mut v___y_6781_: *mut LeanObject,
    mut v___y_6782_: *mut LeanObject,
    mut v___y_6783_: *mut LeanObject,
    mut v___y_6784_: *mut LeanObject,
    mut v___y_6785_: *mut LeanObject,
    mut v___y_6786_: *mut LeanObject,
    mut v___y_6787_: *mut LeanObject,
    mut v___y_6788_: *mut LeanObject,
    mut v___y_6789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6790_: *mut LeanObject = core::ptr::null_mut();
    v_res_6790_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v_x_6779_, v_mkInfoTree_6780_, v___y_6781_, v___y_6782_, v___y_6783_, v___y_6784_, v___y_6785_, v___y_6786_, v___y_6787_, v___y_6788_);
    lean_dec(v___y_6788_);
    lean_dec_ref(v___y_6787_);
    lean_dec(v___y_6786_);
    lean_dec_ref(v___y_6785_);
    lean_dec(v___y_6784_);
    lean_dec_ref(v___y_6783_);
    lean_dec(v___y_6782_);
    lean_dec_ref(v___y_6781_);
    return v_res_6790_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(
    mut v___f_6842_: *mut LeanObject,
    mut v___f_6843_: *mut LeanObject,
    mut v_stx_6844_: *mut LeanObject,
    mut v___y_6845_: *mut LeanObject,
    mut v___y_6846_: *mut LeanObject,
    mut v___y_6847_: *mut LeanObject,
    mut v___y_6848_: *mut LeanObject,
    mut v___y_6849_: *mut LeanObject,
    mut v___y_6850_: *mut LeanObject,
    mut v___y_6851_: *mut LeanObject,
    mut v___y_6852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6854_: *mut LeanObject = core::ptr::null_mut();
    v___x_6854_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v___f_6842_, v___f_6843_, v___y_6845_, v___y_6846_, v___y_6847_, v___y_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_);
    if lean_obj_tag(v___x_6854_) == 0 {
        let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_6854_, 1);
        v___x_6855_ = lean_unsigned_to_nat(1);
        v___x_6856_ = l_Lean_Syntax_getArg(v_stx_6844_, v___x_6855_);
        v___x_6857_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(
            v___x_6856_,
            v___y_6845_,
            v___y_6846_,
            v___y_6847_,
            v___y_6848_,
            v___y_6849_,
            v___y_6850_,
            v___y_6851_,
            v___y_6852_,
        );
        lean_dec(v___x_6856_);
        if lean_obj_tag(v___x_6857_) == 0 {
            let mut v_ref_6858_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6859_: u8 = 0;
            let mut v___x_6860_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6861_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6862_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6863_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6864_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6865_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6866_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6867_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6868_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6869_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6870_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6871_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6872_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6874_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6875_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6879_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6882_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6883_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6886_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6887_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6889_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6890_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6891_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6893_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6894_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6897_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6898_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_6857_, 1);
            v_ref_6858_ = lean_ctor_get(v___y_6851_, 5);
            v___x_6859_ = 0;
            v___x_6860_ = l_Lean_SourceInfo_fromRef(v_ref_6858_, v___x_6859_);
            v___x_6861_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1;
            v___x_6862_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2;
            lean_inc_n(v___x_6860_, 22);
            v___x_6863_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_6863_, 0, v___x_6860_);
            lean_ctor_set(v___x_6863_, 1, v___x_6862_);
            v___x_6864_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4;
            v___x_6865_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6;
            v___x_6866_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8;
            v___x_6867_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10;
            v___x_6868_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11;
            v___x_6869_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_6869_, 0, v___x_6860_);
            lean_ctor_set(v___x_6869_, 1, v___x_6868_);
            v___x_6870_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13;
            v___x_6871_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14;
            v___x_6872_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_6872_, 0, v___x_6860_);
            lean_ctor_set(v___x_6872_, 1, v___x_6871_);
            v___x_6873_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16;
            v___x_6874_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17;
            v___x_6875_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_6875_, 0, v___x_6860_);
            lean_ctor_set(v___x_6875_, 1, v___x_6874_);
            v___x_6876_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19;
            v___x_6877_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20;
            v___x_6878_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_6878_, 0, v___x_6860_);
            lean_ctor_set(v___x_6878_, 1, v___x_6877_);
            v___x_6879_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6876_, v___x_6878_);
            v___x_6880_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6866_, v___x_6879_);
            v___x_6881_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6865_, v___x_6880_);
            v___x_6882_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6864_, v___x_6881_);
            v___x_6883_ = l_Lean_Syntax_node2(v___x_6860_, v___x_6873_, v___x_6875_, v___x_6882_);
            v___x_6884_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6866_, v___x_6883_);
            v___x_6885_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6865_, v___x_6884_);
            v___x_6886_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6864_, v___x_6885_);
            v___x_6887_ = l_Lean_Syntax_node2(v___x_6860_, v___x_6870_, v___x_6872_, v___x_6886_);
            v___x_6888_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6866_, v___x_6887_);
            v___x_6889_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6865_, v___x_6888_);
            v___x_6890_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6864_, v___x_6889_);
            v___x_6891_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21;
            v___x_6892_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_6892_, 0, v___x_6860_);
            lean_ctor_set(v___x_6892_, 1, v___x_6891_);
            v___x_6893_ = l_Lean_Syntax_node3(
                v___x_6860_,
                v___x_6867_,
                v___x_6869_,
                v___x_6890_,
                v___x_6892_,
            );
            v___x_6894_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6866_, v___x_6893_);
            v___x_6895_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6865_, v___x_6894_);
            v___x_6896_ = l_Lean_Syntax_node1(v___x_6860_, v___x_6864_, v___x_6895_);
            v___x_6897_ = l_Lean_Syntax_node2(v___x_6860_, v___x_6861_, v___x_6863_, v___x_6896_);
            v___x_6898_ = l_Lean_Elab_Tactic_evalTactic(
                v___x_6897_,
                v___y_6845_,
                v___y_6846_,
                v___y_6847_,
                v___y_6848_,
                v___y_6849_,
                v___y_6850_,
                v___y_6851_,
                v___y_6852_,
            );
            return v___x_6898_;
        } else {
            return v___x_6857_;
        }
    } else {
        return v___x_6854_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed(
    mut v___f_6899_: *mut LeanObject,
    mut v___f_6900_: *mut LeanObject,
    mut v_stx_6901_: *mut LeanObject,
    mut v___y_6902_: *mut LeanObject,
    mut v___y_6903_: *mut LeanObject,
    mut v___y_6904_: *mut LeanObject,
    mut v___y_6905_: *mut LeanObject,
    mut v___y_6906_: *mut LeanObject,
    mut v___y_6907_: *mut LeanObject,
    mut v___y_6908_: *mut LeanObject,
    mut v___y_6909_: *mut LeanObject,
    mut v___y_6910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6911_: *mut LeanObject = core::ptr::null_mut();
    v_res_6911_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(
        v___f_6899_,
        v___f_6900_,
        v_stx_6901_,
        v___y_6902_,
        v___y_6903_,
        v___y_6904_,
        v___y_6905_,
        v___y_6906_,
        v___y_6907_,
        v___y_6908_,
        v___y_6909_,
    );
    lean_dec(v___y_6909_);
    lean_dec_ref(v___y_6908_);
    lean_dec(v___y_6907_);
    lean_dec_ref(v___y_6906_);
    lean_dec(v___y_6905_);
    lean_dec_ref(v___y_6904_);
    lean_dec(v___y_6903_);
    lean_dec_ref(v___y_6902_);
    lean_dec(v_stx_6901_);
    return v_res_6911_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(
    mut v_stx_6914_: *mut LeanObject,
    mut v_a_6915_: *mut LeanObject,
    mut v_a_6916_: *mut LeanObject,
    mut v_a_6917_: *mut LeanObject,
    mut v_a_6918_: *mut LeanObject,
    mut v_a_6919_: *mut LeanObject,
    mut v_a_6920_: *mut LeanObject,
    mut v_a_6921_: *mut LeanObject,
    mut v_a_6922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6940_: u8 = 0;
    let mut v_cancelTk_x3f_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6942_: u8 = 0;
    let mut v_inheritedTraceOptions_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6955_: u8 = 0;
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6924_ = lean_unsigned_to_nat(0);
                v___x_6925_ = l_Lean_Syntax_getArg(v_stx_6914_, v___x_6924_);
                v___x_6926_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(
                    v___x_6925_,
                    v_a_6915_,
                    v_a_6916_,
                    v_a_6917_,
                    v_a_6918_,
                    v_a_6919_,
                    v_a_6920_,
                    v_a_6921_,
                    v_a_6922_,
                );
                if lean_obj_tag(v___x_6926_) == 0 {
                    v_a_6927_ = lean_ctor_get(v___x_6926_, 0);
                    lean_inc(v_a_6927_);
                    lean_dec_ref_known(v___x_6926_, 1);
                    v_fileName_6928_ = lean_ctor_get(v_a_6921_, 0);
                    v_fileMap_6929_ = lean_ctor_get(v_a_6921_, 1);
                    v_options_6930_ = lean_ctor_get(v_a_6921_, 2);
                    v_currRecDepth_6931_ = lean_ctor_get(v_a_6921_, 3);
                    v_maxRecDepth_6932_ = lean_ctor_get(v_a_6921_, 4);
                    v_ref_6933_ = lean_ctor_get(v_a_6921_, 5);
                    v_currNamespace_6934_ = lean_ctor_get(v_a_6921_, 6);
                    v_openDecls_6935_ = lean_ctor_get(v_a_6921_, 7);
                    v_initHeartbeats_6936_ = lean_ctor_get(v_a_6921_, 8);
                    v_maxHeartbeats_6937_ = lean_ctor_get(v_a_6921_, 9);
                    v_quotContext_6938_ = lean_ctor_get(v_a_6921_, 10);
                    v_currMacroScope_6939_ = lean_ctor_get(v_a_6921_, 11);
                    v_diag_6940_ = lean_ctor_get_uint8(
                        v_a_6921_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_6941_ = lean_ctor_get(v_a_6921_, 12);
                    v_suppressElabErrors_6942_ = lean_ctor_get_uint8(
                        v_a_6921_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_6943_ = lean_ctor_get(v_a_6921_, 13);
                    v___f_6944_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    lean_closure_set(v___f_6944_, 0, v_a_6927_);
                    v___x_6945_ = lean_unsigned_to_nat(2);
                    v___x_6946_ = l_Lean_Syntax_getArg(v_stx_6914_, v___x_6945_);
                    v___f_6947_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0;
                    v___f_6948_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed
                            as *mut core::ffi::c_void,
                        12,
                        3,
                    );
                    lean_closure_set(v___f_6948_, 0, v___f_6947_);
                    lean_closure_set(v___f_6948_, 1, v___f_6944_);
                    lean_closure_set(v___f_6948_, 2, v_stx_6914_);
                    v_ref_6949_ = l_Lean_replaceRef(v___x_6946_, v_ref_6933_);
                    lean_dec(v___x_6946_);
                    lean_inc_ref(v_inheritedTraceOptions_6943_);
                    lean_inc(v_cancelTk_x3f_6941_);
                    lean_inc(v_currMacroScope_6939_);
                    lean_inc(v_quotContext_6938_);
                    lean_inc(v_maxHeartbeats_6937_);
                    lean_inc(v_initHeartbeats_6936_);
                    lean_inc(v_openDecls_6935_);
                    lean_inc(v_currNamespace_6934_);
                    lean_inc(v_maxRecDepth_6932_);
                    lean_inc(v_currRecDepth_6931_);
                    lean_inc_ref(v_options_6930_);
                    lean_inc_ref(v_fileMap_6929_);
                    lean_inc_ref(v_fileName_6928_);
                    v___x_6950_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v___x_6950_, 0, v_fileName_6928_);
                    lean_ctor_set(v___x_6950_, 1, v_fileMap_6929_);
                    lean_ctor_set(v___x_6950_, 2, v_options_6930_);
                    lean_ctor_set(v___x_6950_, 3, v_currRecDepth_6931_);
                    lean_ctor_set(v___x_6950_, 4, v_maxRecDepth_6932_);
                    lean_ctor_set(v___x_6950_, 5, v_ref_6949_);
                    lean_ctor_set(v___x_6950_, 6, v_currNamespace_6934_);
                    lean_ctor_set(v___x_6950_, 7, v_openDecls_6935_);
                    lean_ctor_set(v___x_6950_, 8, v_initHeartbeats_6936_);
                    lean_ctor_set(v___x_6950_, 9, v_maxHeartbeats_6937_);
                    lean_ctor_set(v___x_6950_, 10, v_quotContext_6938_);
                    lean_ctor_set(v___x_6950_, 11, v_currMacroScope_6939_);
                    lean_ctor_set(v___x_6950_, 12, v_cancelTk_x3f_6941_);
                    lean_ctor_set(v___x_6950_, 13, v_inheritedTraceOptions_6943_);
                    lean_ctor_set_uint8(
                        v___x_6950_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        v_diag_6940_,
                    );
                    lean_ctor_set_uint8(
                        v___x_6950_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_6942_,
                    );
                    v___x_6951_ = l_Lean_Elab_Tactic_closeUsingOrAdmit(
                        v___f_6948_,
                        v_a_6915_,
                        v_a_6916_,
                        v_a_6917_,
                        v_a_6918_,
                        v_a_6919_,
                        v_a_6920_,
                        v___x_6950_,
                        v_a_6922_,
                    );
                    lean_dec_ref_known(v___x_6950_, 14);
                    return v___x_6951_;
                } else {
                    lean_dec(v_stx_6914_);
                    v_a_6952_ = lean_ctor_get(v___x_6926_, 0);
                    v_isSharedCheck_6959_ = (!lean_is_exclusive(v___x_6926_)) as u8;
                    if v_isSharedCheck_6959_ == 0 {
                        v___x_6954_ = v___x_6926_;
                        v_isShared_6955_ = v_isSharedCheck_6959_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6952_);
                        lean_dec(v___x_6926_);
                        v___x_6954_ = lean_box(0);
                        v_isShared_6955_ = v_isSharedCheck_6959_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6955_ == 0 {
                    v___x_6957_ = v___x_6954_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6958_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6958_, 0, v_a_6952_);
                    v___x_6957_ = v_reuseFailAlloc_6958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed(
    mut v_stx_6960_: *mut LeanObject,
    mut v_a_6961_: *mut LeanObject,
    mut v_a_6962_: *mut LeanObject,
    mut v_a_6963_: *mut LeanObject,
    mut v_a_6964_: *mut LeanObject,
    mut v_a_6965_: *mut LeanObject,
    mut v_a_6966_: *mut LeanObject,
    mut v_a_6967_: *mut LeanObject,
    mut v_a_6968_: *mut LeanObject,
    mut v_a_6969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6970_: *mut LeanObject = core::ptr::null_mut();
    v_res_6970_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(
        v_stx_6960_,
        v_a_6961_,
        v_a_6962_,
        v_a_6963_,
        v_a_6964_,
        v_a_6965_,
        v_a_6966_,
        v_a_6967_,
        v_a_6968_,
    );
    lean_dec(v_a_6968_);
    lean_dec_ref(v_a_6967_);
    lean_dec(v_a_6966_);
    lean_dec_ref(v_a_6965_);
    lean_dec(v_a_6964_);
    lean_dec_ref(v_a_6963_);
    lean_dec(v_a_6962_);
    lean_dec_ref(v_a_6961_);
    return v_res_6970_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(
    mut v___y_6971_: *mut LeanObject,
    mut v___y_6972_: *mut LeanObject,
    mut v___y_6973_: *mut LeanObject,
    mut v___y_6974_: *mut LeanObject,
    mut v___y_6975_: *mut LeanObject,
    mut v___y_6976_: *mut LeanObject,
    mut v___y_6977_: *mut LeanObject,
    mut v___y_6978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6980_: *mut LeanObject = core::ptr::null_mut();
    v___x_6980_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_6978_);
    return v___x_6980_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___boxed(
    mut v___y_6981_: *mut LeanObject,
    mut v___y_6982_: *mut LeanObject,
    mut v___y_6983_: *mut LeanObject,
    mut v___y_6984_: *mut LeanObject,
    mut v___y_6985_: *mut LeanObject,
    mut v___y_6986_: *mut LeanObject,
    mut v___y_6987_: *mut LeanObject,
    mut v___y_6988_: *mut LeanObject,
    mut v___y_6989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6990_: *mut LeanObject = core::ptr::null_mut();
    v_res_6990_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(v___y_6981_, v___y_6982_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_, v___y_6987_, v___y_6988_);
    lean_dec(v___y_6988_);
    lean_dec_ref(v___y_6987_);
    lean_dec(v___y_6986_);
    lean_dec_ref(v___y_6985_);
    lean_dec(v___y_6984_);
    lean_dec_ref(v___y_6983_);
    lean_dec(v___y_6982_);
    lean_dec_ref(v___y_6981_);
    return v_res_6990_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(
    mut v_00_u03b1_6991_: *mut LeanObject,
    mut v_x_6992_: *mut LeanObject,
    mut v_mkInfoTree_6993_: *mut LeanObject,
    mut v___y_6994_: *mut LeanObject,
    mut v___y_6995_: *mut LeanObject,
    mut v___y_6996_: *mut LeanObject,
    mut v___y_6997_: *mut LeanObject,
    mut v___y_6998_: *mut LeanObject,
    mut v___y_6999_: *mut LeanObject,
    mut v___y_7000_: *mut LeanObject,
    mut v___y_7001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
    v___x_7003_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v_x_6992_, v_mkInfoTree_6993_, v___y_6994_, v___y_6995_, v___y_6996_, v___y_6997_, v___y_6998_, v___y_6999_, v___y_7000_, v___y_7001_);
    return v___x_7003_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___boxed(
    mut v_00_u03b1_7004_: *mut LeanObject,
    mut v_x_7005_: *mut LeanObject,
    mut v_mkInfoTree_7006_: *mut LeanObject,
    mut v___y_7007_: *mut LeanObject,
    mut v___y_7008_: *mut LeanObject,
    mut v___y_7009_: *mut LeanObject,
    mut v___y_7010_: *mut LeanObject,
    mut v___y_7011_: *mut LeanObject,
    mut v___y_7012_: *mut LeanObject,
    mut v___y_7013_: *mut LeanObject,
    mut v___y_7014_: *mut LeanObject,
    mut v___y_7015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7016_: *mut LeanObject = core::ptr::null_mut();
    v_res_7016_ =
        l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(
            v_00_u03b1_7004_,
            v_x_7005_,
            v_mkInfoTree_7006_,
            v___y_7007_,
            v___y_7008_,
            v___y_7009_,
            v___y_7010_,
            v___y_7011_,
            v___y_7012_,
            v___y_7013_,
            v___y_7014_,
        );
    lean_dec(v___y_7014_);
    lean_dec_ref(v___y_7013_);
    lean_dec(v___y_7012_);
    lean_dec_ref(v___y_7011_);
    lean_dec(v___y_7010_);
    lean_dec_ref(v___y_7009_);
    lean_dec(v___y_7008_);
    lean_dec_ref(v___y_7007_);
    return v_res_7016_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1()
-> *mut LeanObject {
    let mut v___x_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    v___x_7032_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7033_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1;
    v___x_7034_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3;
    v___x_7035_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7036_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7032_,
        v___x_7033_,
        v___x_7034_,
        v___x_7035_,
    );
    return v___x_7036_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___boxed(
    mut v_a_7037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7038_: *mut LeanObject = core::ptr::null_mut();
    v_res_7038_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
    return v_res_7038_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3()
-> *mut LeanObject {
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    v___x_7065_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3;
    v___x_7066_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6;
    v___x_7067_ = l_Lean_addBuiltinDeclarationRanges(v___x_7065_, v___x_7066_);
    return v___x_7067_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___boxed(
    mut v_a_7068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7069_: *mut LeanObject = core::ptr::null_mut();
    v_res_7069_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
    return v_res_7069_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalNestedConv(
    mut v_stx_7070_: *mut LeanObject,
    mut v_a_7071_: *mut LeanObject,
    mut v_a_7072_: *mut LeanObject,
    mut v_a_7073_: *mut LeanObject,
    mut v_a_7074_: *mut LeanObject,
    mut v_a_7075_: *mut LeanObject,
    mut v_a_7076_: *mut LeanObject,
    mut v_a_7077_: *mut LeanObject,
    mut v_a_7078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut LeanObject = core::ptr::null_mut();
    v___x_7080_ = lean_unsigned_to_nat(0);
    v___x_7081_ = l_Lean_Syntax_getArg(v_stx_7070_, v___x_7080_);
    v___x_7082_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(
        v___x_7081_,
        v_a_7071_,
        v_a_7072_,
        v_a_7073_,
        v_a_7074_,
        v_a_7075_,
        v_a_7076_,
        v_a_7077_,
        v_a_7078_,
    );
    return v___x_7082_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed(
    mut v_stx_7083_: *mut LeanObject,
    mut v_a_7084_: *mut LeanObject,
    mut v_a_7085_: *mut LeanObject,
    mut v_a_7086_: *mut LeanObject,
    mut v_a_7087_: *mut LeanObject,
    mut v_a_7088_: *mut LeanObject,
    mut v_a_7089_: *mut LeanObject,
    mut v_a_7090_: *mut LeanObject,
    mut v_a_7091_: *mut LeanObject,
    mut v_a_7092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7093_: *mut LeanObject = core::ptr::null_mut();
    v_res_7093_ = l_Lean_Elab_Tactic_Conv_evalNestedConv(
        v_stx_7083_,
        v_a_7084_,
        v_a_7085_,
        v_a_7086_,
        v_a_7087_,
        v_a_7088_,
        v_a_7089_,
        v_a_7090_,
        v_a_7091_,
    );
    lean_dec(v_a_7091_);
    lean_dec_ref(v_a_7090_);
    lean_dec(v_a_7089_);
    lean_dec_ref(v_a_7088_);
    lean_dec(v_a_7087_);
    lean_dec_ref(v_a_7086_);
    lean_dec(v_a_7085_);
    lean_dec_ref(v_a_7084_);
    lean_dec(v_stx_7083_);
    return v_res_7093_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1()
-> *mut LeanObject {
    let mut v___x_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    v___x_7109_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7110_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1;
    v___x_7111_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3;
    v___x_7112_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7113_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7109_,
        v___x_7110_,
        v___x_7111_,
        v___x_7112_,
    );
    return v___x_7113_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___boxed(
    mut v_a_7114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7115_: *mut LeanObject = core::ptr::null_mut();
    v_res_7115_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
    return v_res_7115_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3()
-> *mut LeanObject {
    let mut v___x_7142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut LeanObject = core::ptr::null_mut();
    v___x_7142_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3;
    v___x_7143_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6;
    v___x_7144_ = l_Lean_addBuiltinDeclarationRanges(v___x_7142_, v___x_7143_);
    return v___x_7144_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___boxed(
    mut v_a_7145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7146_: *mut LeanObject = core::ptr::null_mut();
    v_res_7146_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
    return v_res_7146_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeq(
    mut v_stx_7147_: *mut LeanObject,
    mut v_a_7148_: *mut LeanObject,
    mut v_a_7149_: *mut LeanObject,
    mut v_a_7150_: *mut LeanObject,
    mut v_a_7151_: *mut LeanObject,
    mut v_a_7152_: *mut LeanObject,
    mut v_a_7153_: *mut LeanObject,
    mut v_a_7154_: *mut LeanObject,
    mut v_a_7155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    v___x_7157_ = lean_unsigned_to_nat(0);
    v___x_7158_ = l_Lean_Syntax_getArg(v_stx_7147_, v___x_7157_);
    v___x_7159_ = l_Lean_Elab_Tactic_evalTactic(
        v___x_7158_,
        v_a_7148_,
        v_a_7149_,
        v_a_7150_,
        v_a_7151_,
        v_a_7152_,
        v_a_7153_,
        v_a_7154_,
        v_a_7155_,
    );
    return v___x_7159_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed(
    mut v_stx_7160_: *mut LeanObject,
    mut v_a_7161_: *mut LeanObject,
    mut v_a_7162_: *mut LeanObject,
    mut v_a_7163_: *mut LeanObject,
    mut v_a_7164_: *mut LeanObject,
    mut v_a_7165_: *mut LeanObject,
    mut v_a_7166_: *mut LeanObject,
    mut v_a_7167_: *mut LeanObject,
    mut v_a_7168_: *mut LeanObject,
    mut v_a_7169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7170_: *mut LeanObject = core::ptr::null_mut();
    v_res_7170_ = l_Lean_Elab_Tactic_Conv_evalConvSeq(
        v_stx_7160_,
        v_a_7161_,
        v_a_7162_,
        v_a_7163_,
        v_a_7164_,
        v_a_7165_,
        v_a_7166_,
        v_a_7167_,
        v_a_7168_,
    );
    lean_dec(v_a_7168_);
    lean_dec_ref(v_a_7167_);
    lean_dec(v_a_7166_);
    lean_dec_ref(v_a_7165_);
    lean_dec(v_a_7164_);
    lean_dec_ref(v_a_7163_);
    lean_dec(v_a_7162_);
    lean_dec_ref(v_a_7161_);
    lean_dec(v_stx_7160_);
    return v_res_7170_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1()
-> *mut LeanObject {
    let mut v___x_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut LeanObject = core::ptr::null_mut();
    v___x_7186_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7187_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1;
    v___x_7188_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3;
    v___x_7189_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7190_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7186_,
        v___x_7187_,
        v___x_7188_,
        v___x_7189_,
    );
    return v___x_7190_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___boxed(
    mut v_a_7191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7192_: *mut LeanObject = core::ptr::null_mut();
    v_res_7192_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
    return v_res_7192_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3()
-> *mut LeanObject {
    let mut v___x_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
    v___x_7219_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3;
    v___x_7220_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6;
    v___x_7221_ = l_Lean_addBuiltinDeclarationRanges(v___x_7219_, v___x_7220_);
    return v___x_7221_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___boxed(
    mut v_a_7222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7223_: *mut LeanObject = core::ptr::null_mut();
    v_res_7223_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
    return v_res_7223_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(
    mut v_stx_7224_: *mut LeanObject,
    mut v___y_7225_: *mut LeanObject,
    mut v___y_7226_: *mut LeanObject,
    mut v___y_7227_: *mut LeanObject,
    mut v___y_7228_: *mut LeanObject,
    mut v___y_7229_: *mut LeanObject,
    mut v___y_7230_: *mut LeanObject,
    mut v___y_7231_: *mut LeanObject,
    mut v___y_7232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7249_: u8 = 0;
    let mut v___x_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7253_: u8 = 0;
    let mut v_a_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7257_: u8 = 0;
    let mut v___x_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7261_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7234_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_7226_,
                    v___y_7229_,
                    v___y_7230_,
                    v___y_7231_,
                    v___y_7232_,
                );
                if lean_obj_tag(v___x_7234_) == 0 {
                    v_a_7235_ = lean_ctor_get(v___x_7234_, 0);
                    lean_inc(v_a_7235_);
                    lean_dec_ref_known(v___x_7234_, 1);
                    v___x_7236_ = lean_unsigned_to_nat(2);
                    v___x_7237_ = l_Lean_Syntax_getArg(v_stx_7224_, v___x_7236_);
                    v___x_7238_ = lean_unsigned_to_nat(0);
                    v___x_7239_ = l_Lean_Syntax_getArg(v___x_7237_, v___x_7238_);
                    lean_dec(v___x_7237_);
                    v___x_7240_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalTactic___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___x_7240_, 0, v___x_7239_);
                    v___x_7241_ = l_Lean_Elab_Tactic_Conv_convert(
                        v_a_7235_,
                        v___x_7240_,
                        v___y_7225_,
                        v___y_7226_,
                        v___y_7227_,
                        v___y_7228_,
                        v___y_7229_,
                        v___y_7230_,
                        v___y_7231_,
                        v___y_7232_,
                    );
                    if lean_obj_tag(v___x_7241_) == 0 {
                        v_a_7242_ = lean_ctor_get(v___x_7241_, 0);
                        lean_inc(v_a_7242_);
                        lean_dec_ref_known(v___x_7241_, 1);
                        v_fst_7243_ = lean_ctor_get(v_a_7242_, 0);
                        lean_inc(v_fst_7243_);
                        v_snd_7244_ = lean_ctor_get(v_a_7242_, 1);
                        lean_inc(v_snd_7244_);
                        lean_dec(v_a_7242_);
                        v___x_7245_ = l_Lean_Elab_Tactic_Conv_updateLhs(
                            v_fst_7243_,
                            v_snd_7244_,
                            v___y_7225_,
                            v___y_7226_,
                            v___y_7227_,
                            v___y_7228_,
                            v___y_7229_,
                            v___y_7230_,
                            v___y_7231_,
                            v___y_7232_,
                        );
                        return v___x_7245_;
                    } else {
                        v_a_7246_ = lean_ctor_get(v___x_7241_, 0);
                        v_isSharedCheck_7253_ = (!lean_is_exclusive(v___x_7241_)) as u8;
                        if v_isSharedCheck_7253_ == 0 {
                            v___x_7248_ = v___x_7241_;
                            v_isShared_7249_ = v_isSharedCheck_7253_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7246_);
                            lean_dec(v___x_7241_);
                            v___x_7248_ = lean_box(0);
                            v_isShared_7249_ = v_isSharedCheck_7253_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_7254_ = lean_ctor_get(v___x_7234_, 0);
                    v_isSharedCheck_7261_ = (!lean_is_exclusive(v___x_7234_)) as u8;
                    if v_isSharedCheck_7261_ == 0 {
                        v___x_7256_ = v___x_7234_;
                        v_isShared_7257_ = v_isSharedCheck_7261_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7254_);
                        lean_dec(v___x_7234_);
                        v___x_7256_ = lean_box(0);
                        v_isShared_7257_ = v_isSharedCheck_7261_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7249_ == 0 {
                    v___x_7251_ = v___x_7248_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7252_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7252_, 0, v_a_7246_);
                    v___x_7251_ = v_reuseFailAlloc_7252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7251_;
            }
            3 => {
                if v_isShared_7257_ == 0 {
                    v___x_7259_ = v___x_7256_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7260_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7260_, 0, v_a_7254_);
                    v___x_7259_ = v_reuseFailAlloc_7260_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7259_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed(
    mut v_stx_7262_: *mut LeanObject,
    mut v___y_7263_: *mut LeanObject,
    mut v___y_7264_: *mut LeanObject,
    mut v___y_7265_: *mut LeanObject,
    mut v___y_7266_: *mut LeanObject,
    mut v___y_7267_: *mut LeanObject,
    mut v___y_7268_: *mut LeanObject,
    mut v___y_7269_: *mut LeanObject,
    mut v___y_7270_: *mut LeanObject,
    mut v___y_7271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7272_: *mut LeanObject = core::ptr::null_mut();
    v_res_7272_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(
        v_stx_7262_,
        v___y_7263_,
        v___y_7264_,
        v___y_7265_,
        v___y_7266_,
        v___y_7267_,
        v___y_7268_,
        v___y_7269_,
        v___y_7270_,
    );
    lean_dec(v___y_7270_);
    lean_dec_ref(v___y_7269_);
    lean_dec(v___y_7268_);
    lean_dec_ref(v___y_7267_);
    lean_dec(v___y_7266_);
    lean_dec_ref(v___y_7265_);
    lean_dec(v___y_7264_);
    lean_dec_ref(v___y_7263_);
    lean_dec(v_stx_7262_);
    return v_res_7272_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvConvSeq(
    mut v_stx_7273_: *mut LeanObject,
    mut v_a_7274_: *mut LeanObject,
    mut v_a_7275_: *mut LeanObject,
    mut v_a_7276_: *mut LeanObject,
    mut v_a_7277_: *mut LeanObject,
    mut v_a_7278_: *mut LeanObject,
    mut v_a_7279_: *mut LeanObject,
    mut v_a_7280_: *mut LeanObject,
    mut v_a_7281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: *mut LeanObject = core::ptr::null_mut();
    v___f_7283_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    lean_closure_set(v___f_7283_, 0, v_stx_7273_);
    v___x_7284_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_7283_,
        v_a_7274_,
        v_a_7275_,
        v_a_7276_,
        v_a_7277_,
        v_a_7278_,
        v_a_7279_,
        v_a_7280_,
        v_a_7281_,
    );
    return v___x_7284_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed(
    mut v_stx_7285_: *mut LeanObject,
    mut v_a_7286_: *mut LeanObject,
    mut v_a_7287_: *mut LeanObject,
    mut v_a_7288_: *mut LeanObject,
    mut v_a_7289_: *mut LeanObject,
    mut v_a_7290_: *mut LeanObject,
    mut v_a_7291_: *mut LeanObject,
    mut v_a_7292_: *mut LeanObject,
    mut v_a_7293_: *mut LeanObject,
    mut v_a_7294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7295_: *mut LeanObject = core::ptr::null_mut();
    v_res_7295_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq(
        v_stx_7285_,
        v_a_7286_,
        v_a_7287_,
        v_a_7288_,
        v_a_7289_,
        v_a_7290_,
        v_a_7291_,
        v_a_7292_,
        v_a_7293_,
    );
    lean_dec(v_a_7293_);
    lean_dec_ref(v_a_7292_);
    lean_dec(v_a_7291_);
    lean_dec_ref(v_a_7290_);
    lean_dec(v_a_7289_);
    lean_dec_ref(v_a_7288_);
    lean_dec(v_a_7287_);
    lean_dec_ref(v_a_7286_);
    return v_res_7295_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1()
-> *mut LeanObject {
    let mut v___x_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut LeanObject = core::ptr::null_mut();
    v___x_7311_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7312_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1;
    v___x_7313_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3;
    v___x_7314_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7315_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7311_,
        v___x_7312_,
        v___x_7313_,
        v___x_7314_,
    );
    return v___x_7315_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___boxed(
    mut v_a_7316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7317_: *mut LeanObject = core::ptr::null_mut();
    v_res_7317_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
    return v_res_7317_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3()
-> *mut LeanObject {
    let mut v___x_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut LeanObject = core::ptr::null_mut();
    v___x_7344_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3;
    v___x_7345_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6;
    v___x_7346_ = l_Lean_addBuiltinDeclarationRanges(v___x_7344_, v___x_7345_);
    return v___x_7346_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___boxed(
    mut v_a_7347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7348_: *mut LeanObject = core::ptr::null_mut();
    v_res_7348_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
    return v_res_7348_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalParen(
    mut v_stx_7349_: *mut LeanObject,
    mut v_a_7350_: *mut LeanObject,
    mut v_a_7351_: *mut LeanObject,
    mut v_a_7352_: *mut LeanObject,
    mut v_a_7353_: *mut LeanObject,
    mut v_a_7354_: *mut LeanObject,
    mut v_a_7355_: *mut LeanObject,
    mut v_a_7356_: *mut LeanObject,
    mut v_a_7357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    v___x_7359_ = lean_unsigned_to_nat(1);
    v___x_7360_ = l_Lean_Syntax_getArg(v_stx_7349_, v___x_7359_);
    v___x_7361_ = l_Lean_Elab_Tactic_evalTactic(
        v___x_7360_,
        v_a_7350_,
        v_a_7351_,
        v_a_7352_,
        v_a_7353_,
        v_a_7354_,
        v_a_7355_,
        v_a_7356_,
        v_a_7357_,
    );
    return v___x_7361_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalParen___boxed(
    mut v_stx_7362_: *mut LeanObject,
    mut v_a_7363_: *mut LeanObject,
    mut v_a_7364_: *mut LeanObject,
    mut v_a_7365_: *mut LeanObject,
    mut v_a_7366_: *mut LeanObject,
    mut v_a_7367_: *mut LeanObject,
    mut v_a_7368_: *mut LeanObject,
    mut v_a_7369_: *mut LeanObject,
    mut v_a_7370_: *mut LeanObject,
    mut v_a_7371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7372_: *mut LeanObject = core::ptr::null_mut();
    v_res_7372_ = l_Lean_Elab_Tactic_Conv_evalParen(
        v_stx_7362_,
        v_a_7363_,
        v_a_7364_,
        v_a_7365_,
        v_a_7366_,
        v_a_7367_,
        v_a_7368_,
        v_a_7369_,
        v_a_7370_,
    );
    lean_dec(v_a_7370_);
    lean_dec_ref(v_a_7369_);
    lean_dec(v_a_7368_);
    lean_dec_ref(v_a_7367_);
    lean_dec(v_a_7366_);
    lean_dec_ref(v_a_7365_);
    lean_dec(v_a_7364_);
    lean_dec_ref(v_a_7363_);
    lean_dec(v_stx_7362_);
    return v_res_7372_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1()
-> *mut LeanObject {
    let mut v___x_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut LeanObject = core::ptr::null_mut();
    v___x_7387_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7388_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0;
    v___x_7389_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2;
    v___x_7390_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalParen___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7391_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7387_,
        v___x_7388_,
        v___x_7389_,
        v___x_7390_,
    );
    return v___x_7391_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___boxed(
    mut v_a_7392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7393_: *mut LeanObject = core::ptr::null_mut();
    v_res_7393_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
    return v_res_7393_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3()
-> *mut LeanObject {
    let mut v___x_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7422_: *mut LeanObject = core::ptr::null_mut();
    v___x_7420_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2;
    v___x_7421_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6;
    v___x_7422_ = l_Lean_addBuiltinDeclarationRanges(v___x_7420_, v___x_7421_);
    return v___x_7422_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___boxed(
    mut v_a_7423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7424_: *mut LeanObject = core::ptr::null_mut();
    v_res_7424_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
    return v_res_7424_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(
    mut v_x_7425_: *mut LeanObject,
    mut v___y_7426_: *mut LeanObject,
    mut v___y_7427_: *mut LeanObject,
    mut v___y_7428_: *mut LeanObject,
    mut v___y_7429_: *mut LeanObject,
    mut v___y_7430_: *mut LeanObject,
    mut v___y_7431_: *mut LeanObject,
    mut v___y_7432_: *mut LeanObject,
    mut v___y_7433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7435_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_7429_);
    lean_inc_ref(v___y_7428_);
    lean_inc(v___y_7427_);
    lean_inc_ref(v___y_7426_);
    v___x_7435_ = lean_apply_9(
        v_x_7425_,
        v___y_7426_,
        v___y_7427_,
        v___y_7428_,
        v___y_7429_,
        v___y_7430_,
        v___y_7431_,
        v___y_7432_,
        v___y_7433_,
        lean_box(0),
    );
    return v___x_7435_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed(
    mut v_x_7436_: *mut LeanObject,
    mut v___y_7437_: *mut LeanObject,
    mut v___y_7438_: *mut LeanObject,
    mut v___y_7439_: *mut LeanObject,
    mut v___y_7440_: *mut LeanObject,
    mut v___y_7441_: *mut LeanObject,
    mut v___y_7442_: *mut LeanObject,
    mut v___y_7443_: *mut LeanObject,
    mut v___y_7444_: *mut LeanObject,
    mut v___y_7445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7446_: *mut LeanObject = core::ptr::null_mut();
    v_res_7446_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(v_x_7436_, v___y_7437_, v___y_7438_, v___y_7439_, v___y_7440_, v___y_7441_, v___y_7442_, v___y_7443_, v___y_7444_);
    lean_dec(v___y_7440_);
    lean_dec_ref(v___y_7439_);
    lean_dec(v___y_7438_);
    lean_dec_ref(v___y_7437_);
    return v_res_7446_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(
    mut v_mvarId_7447_: *mut LeanObject,
    mut v_x_7448_: *mut LeanObject,
    mut v___y_7449_: *mut LeanObject,
    mut v___y_7450_: *mut LeanObject,
    mut v___y_7451_: *mut LeanObject,
    mut v___y_7452_: *mut LeanObject,
    mut v___y_7453_: *mut LeanObject,
    mut v___y_7454_: *mut LeanObject,
    mut v___y_7455_: *mut LeanObject,
    mut v___y_7456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7463_: u8 = 0;
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_7452_);
                lean_inc_ref(v___y_7451_);
                lean_inc(v___y_7450_);
                lean_inc_ref(v___y_7449_);
                v___f_7458_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_7458_, 0, v_x_7448_);
                lean_closure_set(v___f_7458_, 1, v___y_7449_);
                lean_closure_set(v___f_7458_, 2, v___y_7450_);
                lean_closure_set(v___f_7458_, 3, v___y_7451_);
                lean_closure_set(v___f_7458_, 4, v___y_7452_);
                v___x_7459_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_7447_,
                    v___f_7458_,
                    v___y_7453_,
                    v___y_7454_,
                    v___y_7455_,
                    v___y_7456_,
                );
                if lean_obj_tag(v___x_7459_) == 0 {
                    return v___x_7459_;
                } else {
                    v_a_7460_ = lean_ctor_get(v___x_7459_, 0);
                    v_isSharedCheck_7467_ = (!lean_is_exclusive(v___x_7459_)) as u8;
                    if v_isSharedCheck_7467_ == 0 {
                        v___x_7462_ = v___x_7459_;
                        v_isShared_7463_ = v_isSharedCheck_7467_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7460_);
                        lean_dec(v___x_7459_);
                        v___x_7462_ = lean_box(0);
                        v_isShared_7463_ = v_isSharedCheck_7467_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7463_ == 0 {
                    v___x_7465_ = v___x_7462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7466_, 0, v_a_7460_);
                    v___x_7465_ = v_reuseFailAlloc_7466_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___boxed(
    mut v_mvarId_7468_: *mut LeanObject,
    mut v_x_7469_: *mut LeanObject,
    mut v___y_7470_: *mut LeanObject,
    mut v___y_7471_: *mut LeanObject,
    mut v___y_7472_: *mut LeanObject,
    mut v___y_7473_: *mut LeanObject,
    mut v___y_7474_: *mut LeanObject,
    mut v___y_7475_: *mut LeanObject,
    mut v___y_7476_: *mut LeanObject,
    mut v___y_7477_: *mut LeanObject,
    mut v___y_7478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7479_: *mut LeanObject = core::ptr::null_mut();
    v_res_7479_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(
            v_mvarId_7468_,
            v_x_7469_,
            v___y_7470_,
            v___y_7471_,
            v___y_7472_,
            v___y_7473_,
            v___y_7474_,
            v___y_7475_,
            v___y_7476_,
            v___y_7477_,
        );
    lean_dec(v___y_7477_);
    lean_dec_ref(v___y_7476_);
    lean_dec(v___y_7475_);
    lean_dec_ref(v___y_7474_);
    lean_dec(v___y_7473_);
    lean_dec_ref(v___y_7472_);
    lean_dec(v___y_7471_);
    lean_dec_ref(v___y_7470_);
    return v_res_7479_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(
    mut v_00_u03b1_7480_: *mut LeanObject,
    mut v_mvarId_7481_: *mut LeanObject,
    mut v_x_7482_: *mut LeanObject,
    mut v___y_7483_: *mut LeanObject,
    mut v___y_7484_: *mut LeanObject,
    mut v___y_7485_: *mut LeanObject,
    mut v___y_7486_: *mut LeanObject,
    mut v___y_7487_: *mut LeanObject,
    mut v___y_7488_: *mut LeanObject,
    mut v___y_7489_: *mut LeanObject,
    mut v___y_7490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7492_: *mut LeanObject = core::ptr::null_mut();
    v___x_7492_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(
            v_mvarId_7481_,
            v_x_7482_,
            v___y_7483_,
            v___y_7484_,
            v___y_7485_,
            v___y_7486_,
            v___y_7487_,
            v___y_7488_,
            v___y_7489_,
            v___y_7490_,
        );
    return v___x_7492_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___boxed(
    mut v_00_u03b1_7493_: *mut LeanObject,
    mut v_mvarId_7494_: *mut LeanObject,
    mut v_x_7495_: *mut LeanObject,
    mut v___y_7496_: *mut LeanObject,
    mut v___y_7497_: *mut LeanObject,
    mut v___y_7498_: *mut LeanObject,
    mut v___y_7499_: *mut LeanObject,
    mut v___y_7500_: *mut LeanObject,
    mut v___y_7501_: *mut LeanObject,
    mut v___y_7502_: *mut LeanObject,
    mut v___y_7503_: *mut LeanObject,
    mut v___y_7504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7505_: *mut LeanObject = core::ptr::null_mut();
    v_res_7505_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(
        v_00_u03b1_7493_,
        v_mvarId_7494_,
        v_x_7495_,
        v___y_7496_,
        v___y_7497_,
        v___y_7498_,
        v___y_7499_,
        v___y_7500_,
        v___y_7501_,
        v___y_7502_,
        v___y_7503_,
    );
    lean_dec(v___y_7503_);
    lean_dec_ref(v___y_7502_);
    lean_dec(v___y_7501_);
    lean_dec_ref(v___y_7500_);
    lean_dec(v___y_7499_);
    lean_dec_ref(v___y_7498_);
    lean_dec(v___y_7497_);
    lean_dec_ref(v___y_7496_);
    return v_res_7505_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(
    mut v_head_7506_: *mut LeanObject,
    mut v___y_7507_: *mut LeanObject,
    mut v___y_7508_: *mut LeanObject,
    mut v___y_7509_: *mut LeanObject,
    mut v___y_7510_: *mut LeanObject,
    mut v___y_7511_: *mut LeanObject,
    mut v___y_7512_: *mut LeanObject,
    mut v___y_7513_: *mut LeanObject,
    mut v___y_7514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7522_: u8 = 0;
    let mut v_val_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: u8 = 0;
    let mut v___x_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7537_: u8 = 0;
    let mut v___x_7539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7541_: u8 = 0;
    let mut v___x_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7545_: u8 = 0;
    let mut v_a_7546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7549_: u8 = 0;
    let mut v___x_7551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7553_: u8 = 0;
    let mut v_a_7554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7557_: u8 = 0;
    let mut v___x_7559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_head_7506_);
                v___x_7516_ = l_Lean_MVarId_getType(
                    v_head_7506_,
                    v___y_7511_,
                    v___y_7512_,
                    v___y_7513_,
                    v___y_7514_,
                );
                if lean_obj_tag(v___x_7516_) == 0 {
                    v_a_7517_ = lean_ctor_get(v___x_7516_, 0);
                    lean_inc_n(v_a_7517_, 2);
                    lean_dec_ref_known(v___x_7516_, 1);
                    v___x_7518_ = l_Lean_Meta_matchEq_x3f(
                        v_a_7517_,
                        v___y_7511_,
                        v___y_7512_,
                        v___y_7513_,
                        v___y_7514_,
                    );
                    if lean_obj_tag(v___x_7518_) == 0 {
                        v_a_7519_ = lean_ctor_get(v___x_7518_, 0);
                        v_isSharedCheck_7545_ = (!lean_is_exclusive(v___x_7518_)) as u8;
                        if v_isSharedCheck_7545_ == 0 {
                            v___x_7521_ = v___x_7518_;
                            v_isShared_7522_ = v_isSharedCheck_7545_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7519_);
                            lean_dec(v___x_7518_);
                            v___x_7521_ = lean_box(0);
                            v_isShared_7522_ = v_isSharedCheck_7545_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_7517_);
                        lean_dec(v_head_7506_);
                        v_a_7546_ = lean_ctor_get(v___x_7518_, 0);
                        v_isSharedCheck_7553_ = (!lean_is_exclusive(v___x_7518_)) as u8;
                        if v_isSharedCheck_7553_ == 0 {
                            v___x_7548_ = v___x_7518_;
                            v_isShared_7549_ = v_isSharedCheck_7553_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_7546_);
                            lean_dec(v___x_7518_);
                            v___x_7548_ = lean_box(0);
                            v_isShared_7549_ = v_isSharedCheck_7553_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_head_7506_);
                    v_a_7554_ = lean_ctor_get(v___x_7516_, 0);
                    v_isSharedCheck_7561_ = (!lean_is_exclusive(v___x_7516_)) as u8;
                    if v_isSharedCheck_7561_ == 0 {
                        v___x_7556_ = v___x_7516_;
                        v_isShared_7557_ = v_isSharedCheck_7561_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_7554_);
                        lean_dec(v___x_7516_);
                        v___x_7556_ = lean_box(0);
                        v_isShared_7557_ = v_isSharedCheck_7561_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_7519_) == 1 {
                    v_val_7523_ = lean_ctor_get(v_a_7519_, 0);
                    lean_inc(v_val_7523_);
                    lean_dec_ref_known(v_a_7519_, 1);
                    v_snd_7524_ = lean_ctor_get(v_val_7523_, 1);
                    lean_inc(v_snd_7524_);
                    lean_dec(v_val_7523_);
                    v_snd_7525_ = lean_ctor_get(v_snd_7524_, 1);
                    lean_inc(v_snd_7525_);
                    lean_dec(v_snd_7524_);
                    v___x_7526_ = l_Lean_Expr_getAppFn(v_snd_7525_);
                    lean_dec(v_snd_7525_);
                    v___x_7527_ = l_Lean_Expr_isMVar(v___x_7526_);
                    lean_dec_ref(v___x_7526_);
                    if v___x_7527_ == 0 {
                        lean_dec(v_a_7517_);
                        if v_isShared_7522_ == 0 {
                            lean_ctor_set(v___x_7521_, 0, v_head_7506_);
                            v___x_7529_ = v___x_7521_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_7530_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7530_, 0, v_head_7506_);
                            v___x_7529_ = v_reuseFailAlloc_7530_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_7521_);
                        v___x_7531_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal(
                            v_a_7517_,
                            v___y_7511_,
                            v___y_7512_,
                            v___y_7513_,
                            v___y_7514_,
                        );
                        if lean_obj_tag(v___x_7531_) == 0 {
                            v_a_7532_ = lean_ctor_get(v___x_7531_, 0);
                            lean_inc(v_a_7532_);
                            lean_dec_ref_known(v___x_7531_, 1);
                            v___x_7533_ = l_Lean_MVarId_replaceTargetDefEq(
                                v_head_7506_,
                                v_a_7532_,
                                v___y_7511_,
                                v___y_7512_,
                                v___y_7513_,
                                v___y_7514_,
                            );
                            return v___x_7533_;
                        } else {
                            lean_dec(v_head_7506_);
                            v_a_7534_ = lean_ctor_get(v___x_7531_, 0);
                            v_isSharedCheck_7541_ = (!lean_is_exclusive(v___x_7531_)) as u8;
                            if v_isSharedCheck_7541_ == 0 {
                                v___x_7536_ = v___x_7531_;
                                v_isShared_7537_ = v_isSharedCheck_7541_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_7534_);
                                lean_dec(v___x_7531_);
                                v___x_7536_ = lean_box(0);
                                v_isShared_7537_ = v_isSharedCheck_7541_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_7519_);
                    lean_dec(v_a_7517_);
                    if v_isShared_7522_ == 0 {
                        lean_ctor_set(v___x_7521_, 0, v_head_7506_);
                        v___x_7543_ = v___x_7521_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7544_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7544_, 0, v_head_7506_);
                        v___x_7543_ = v_reuseFailAlloc_7544_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7529_;
            }
            3 => {
                if v_isShared_7537_ == 0 {
                    v___x_7539_ = v___x_7536_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7540_, 0, v_a_7534_);
                    v___x_7539_ = v_reuseFailAlloc_7540_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7539_;
            }
            5 => {
                return v___x_7543_;
            }
            6 => {
                if v_isShared_7549_ == 0 {
                    v___x_7551_ = v___x_7548_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7552_, 0, v_a_7546_);
                    v___x_7551_ = v_reuseFailAlloc_7552_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7551_;
            }
            8 => {
                if v_isShared_7557_ == 0 {
                    v___x_7559_ = v___x_7556_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7560_, 0, v_a_7554_);
                    v___x_7559_ = v_reuseFailAlloc_7560_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed(
    mut v_head_7562_: *mut LeanObject,
    mut v___y_7563_: *mut LeanObject,
    mut v___y_7564_: *mut LeanObject,
    mut v___y_7565_: *mut LeanObject,
    mut v___y_7566_: *mut LeanObject,
    mut v___y_7567_: *mut LeanObject,
    mut v___y_7568_: *mut LeanObject,
    mut v___y_7569_: *mut LeanObject,
    mut v___y_7570_: *mut LeanObject,
    mut v___y_7571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7572_: *mut LeanObject = core::ptr::null_mut();
    v_res_7572_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(
        v_head_7562_,
        v___y_7563_,
        v___y_7564_,
        v___y_7565_,
        v___y_7566_,
        v___y_7567_,
        v___y_7568_,
        v___y_7569_,
        v___y_7570_,
    );
    lean_dec(v___y_7570_);
    lean_dec_ref(v___y_7569_);
    lean_dec(v___y_7568_);
    lean_dec_ref(v___y_7567_);
    lean_dec(v___y_7566_);
    lean_dec_ref(v___y_7565_);
    lean_dec(v___y_7564_);
    lean_dec_ref(v___y_7563_);
    return v_res_7572_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(
    mut v_x_7573_: *mut LeanObject,
    mut v_x_7574_: *mut LeanObject,
    mut v___y_7575_: *mut LeanObject,
    mut v___y_7576_: *mut LeanObject,
    mut v___y_7577_: *mut LeanObject,
    mut v___y_7578_: *mut LeanObject,
    mut v___y_7579_: *mut LeanObject,
    mut v___y_7580_: *mut LeanObject,
    mut v___y_7581_: *mut LeanObject,
    mut v___y_7582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7590_: u8 = 0;
    let mut v___f_7591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7601_: u8 = 0;
    let mut v___x_7603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7605_: u8 = 0;
    let mut v_isSharedCheck_7606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7573_) == 0 {
                    v___x_7584_ = l_List_reverse___redArg(v_x_7574_);
                    v___x_7585_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7585_, 0, v___x_7584_);
                    return v___x_7585_;
                } else {
                    v_head_7586_ = lean_ctor_get(v_x_7573_, 0);
                    v_tail_7587_ = lean_ctor_get(v_x_7573_, 1);
                    v_isSharedCheck_7606_ = (!lean_is_exclusive(v_x_7573_)) as u8;
                    if v_isSharedCheck_7606_ == 0 {
                        v___x_7589_ = v_x_7573_;
                        v_isShared_7590_ = v_isSharedCheck_7606_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7587_);
                        lean_inc(v_head_7586_);
                        lean_dec(v_x_7573_);
                        v___x_7589_ = lean_box(0);
                        v_isShared_7590_ = v_isSharedCheck_7606_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_7586_);
                v___f_7591_ = lean_alloc_closure(l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed as *mut core::ffi::c_void, 10, 1);
                lean_closure_set(v___f_7591_, 0, v_head_7586_);
                v___x_7592_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_head_7586_, v___f_7591_, v___y_7575_, v___y_7576_, v___y_7577_, v___y_7578_, v___y_7579_, v___y_7580_, v___y_7581_, v___y_7582_);
                if lean_obj_tag(v___x_7592_) == 0 {
                    v_a_7593_ = lean_ctor_get(v___x_7592_, 0);
                    lean_inc(v_a_7593_);
                    lean_dec_ref_known(v___x_7592_, 1);
                    if v_isShared_7590_ == 0 {
                        lean_ctor_set(v___x_7589_, 1, v_x_7574_);
                        lean_ctor_set(v___x_7589_, 0, v_a_7593_);
                        v___x_7595_ = v___x_7589_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7597_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7597_, 0, v_a_7593_);
                        lean_ctor_set(v_reuseFailAlloc_7597_, 1, v_x_7574_);
                        v___x_7595_ = v_reuseFailAlloc_7597_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7589_);
                    lean_dec(v_tail_7587_);
                    lean_dec(v_x_7574_);
                    v_a_7598_ = lean_ctor_get(v___x_7592_, 0);
                    v_isSharedCheck_7605_ = (!lean_is_exclusive(v___x_7592_)) as u8;
                    if v_isSharedCheck_7605_ == 0 {
                        v___x_7600_ = v___x_7592_;
                        v_isShared_7601_ = v_isSharedCheck_7605_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7598_);
                        lean_dec(v___x_7592_);
                        v___x_7600_ = lean_box(0);
                        v_isShared_7601_ = v_isSharedCheck_7605_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_7573_ = v_tail_7587_;
                v_x_7574_ = v___x_7595_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_7601_ == 0 {
                    v___x_7603_ = v___x_7600_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7604_, 0, v_a_7598_);
                    v___x_7603_ = v_reuseFailAlloc_7604_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___boxed(
    mut v_x_7607_: *mut LeanObject,
    mut v_x_7608_: *mut LeanObject,
    mut v___y_7609_: *mut LeanObject,
    mut v___y_7610_: *mut LeanObject,
    mut v___y_7611_: *mut LeanObject,
    mut v___y_7612_: *mut LeanObject,
    mut v___y_7613_: *mut LeanObject,
    mut v___y_7614_: *mut LeanObject,
    mut v___y_7615_: *mut LeanObject,
    mut v___y_7616_: *mut LeanObject,
    mut v___y_7617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7618_: *mut LeanObject = core::ptr::null_mut();
    v_res_7618_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(
        v_x_7607_,
        v_x_7608_,
        v___y_7609_,
        v___y_7610_,
        v___y_7611_,
        v___y_7612_,
        v___y_7613_,
        v___y_7614_,
        v___y_7615_,
        v___y_7616_,
    );
    lean_dec(v___y_7616_);
    lean_dec_ref(v___y_7615_);
    lean_dec(v___y_7614_);
    lean_dec_ref(v___y_7613_);
    lean_dec(v___y_7612_);
    lean_dec_ref(v___y_7611_);
    lean_dec(v___y_7610_);
    lean_dec_ref(v___y_7609_);
    return v_res_7618_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(
    mut v_a_7619_: *mut LeanObject,
    mut v_a_7620_: *mut LeanObject,
    mut v_a_7621_: *mut LeanObject,
    mut v_a_7622_: *mut LeanObject,
    mut v_a_7623_: *mut LeanObject,
    mut v_a_7624_: *mut LeanObject,
    mut v_a_7625_: *mut LeanObject,
    mut v_a_7626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7637_: u8 = 0;
    let mut v___x_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7641_: u8 = 0;
    let mut v_a_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7645_: u8 = 0;
    let mut v___x_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7628_ = l_Lean_Elab_Tactic_getUnsolvedGoals(
                    v_a_7619_, v_a_7620_, v_a_7621_, v_a_7622_, v_a_7623_, v_a_7624_, v_a_7625_,
                    v_a_7626_,
                );
                if lean_obj_tag(v___x_7628_) == 0 {
                    v_a_7629_ = lean_ctor_get(v___x_7628_, 0);
                    lean_inc(v_a_7629_);
                    lean_dec_ref_known(v___x_7628_, 1);
                    v___x_7630_ = lean_box(0);
                    v___x_7631_ =
                        l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(
                            v_a_7629_,
                            v___x_7630_,
                            v_a_7619_,
                            v_a_7620_,
                            v_a_7621_,
                            v_a_7622_,
                            v_a_7623_,
                            v_a_7624_,
                            v_a_7625_,
                            v_a_7626_,
                        );
                    if lean_obj_tag(v___x_7631_) == 0 {
                        v_a_7632_ = lean_ctor_get(v___x_7631_, 0);
                        lean_inc(v_a_7632_);
                        lean_dec_ref_known(v___x_7631_, 1);
                        v___x_7633_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_7632_, v_a_7620_);
                        return v___x_7633_;
                    } else {
                        v_a_7634_ = lean_ctor_get(v___x_7631_, 0);
                        v_isSharedCheck_7641_ = (!lean_is_exclusive(v___x_7631_)) as u8;
                        if v_isSharedCheck_7641_ == 0 {
                            v___x_7636_ = v___x_7631_;
                            v_isShared_7637_ = v_isSharedCheck_7641_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7634_);
                            lean_dec(v___x_7631_);
                            v___x_7636_ = lean_box(0);
                            v_isShared_7637_ = v_isSharedCheck_7641_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_7642_ = lean_ctor_get(v___x_7628_, 0);
                    v_isSharedCheck_7649_ = (!lean_is_exclusive(v___x_7628_)) as u8;
                    if v_isSharedCheck_7649_ == 0 {
                        v___x_7644_ = v___x_7628_;
                        v_isShared_7645_ = v_isSharedCheck_7649_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7642_);
                        lean_dec(v___x_7628_);
                        v___x_7644_ = lean_box(0);
                        v_isShared_7645_ = v_isSharedCheck_7649_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7637_ == 0 {
                    v___x_7639_ = v___x_7636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7640_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7640_, 0, v_a_7634_);
                    v___x_7639_ = v_reuseFailAlloc_7640_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7639_;
            }
            3 => {
                if v_isShared_7645_ == 0 {
                    v___x_7647_ = v___x_7644_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7648_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7648_, 0, v_a_7642_);
                    v___x_7647_ = v_reuseFailAlloc_7648_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_remarkAsConvGoal___boxed(
    mut v_a_7650_: *mut LeanObject,
    mut v_a_7651_: *mut LeanObject,
    mut v_a_7652_: *mut LeanObject,
    mut v_a_7653_: *mut LeanObject,
    mut v_a_7654_: *mut LeanObject,
    mut v_a_7655_: *mut LeanObject,
    mut v_a_7656_: *mut LeanObject,
    mut v_a_7657_: *mut LeanObject,
    mut v_a_7658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7659_: *mut LeanObject = core::ptr::null_mut();
    v_res_7659_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(
        v_a_7650_, v_a_7651_, v_a_7652_, v_a_7653_, v_a_7654_, v_a_7655_, v_a_7656_, v_a_7657_,
    );
    lean_dec(v_a_7657_);
    lean_dec_ref(v_a_7656_);
    lean_dec(v_a_7655_);
    lean_dec_ref(v_a_7654_);
    lean_dec(v_a_7653_);
    lean_dec_ref(v_a_7652_);
    lean_dec(v_a_7651_);
    lean_dec_ref(v_a_7650_);
    return v_res_7659_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(
    mut v_stx_7660_: *mut LeanObject,
    mut v_a_7661_: *mut LeanObject,
    mut v_a_7662_: *mut LeanObject,
    mut v_a_7663_: *mut LeanObject,
    mut v_a_7664_: *mut LeanObject,
    mut v_a_7665_: *mut LeanObject,
    mut v_a_7666_: *mut LeanObject,
    mut v_a_7667_: *mut LeanObject,
    mut v_a_7668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seq_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: *mut LeanObject = core::ptr::null_mut();
    v___x_7670_ = lean_unsigned_to_nat(2);
    v_seq_7671_ = l_Lean_Syntax_getArg(v_stx_7660_, v___x_7670_);
    v___x_7672_ = l_Lean_Elab_Tactic_evalTactic(
        v_seq_7671_,
        v_a_7661_,
        v_a_7662_,
        v_a_7663_,
        v_a_7664_,
        v_a_7665_,
        v_a_7666_,
        v_a_7667_,
        v_a_7668_,
    );
    if lean_obj_tag(v___x_7672_) == 0 {
        let mut v___x_7673_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_7672_, 1);
        v___x_7673_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(
            v_a_7661_, v_a_7662_, v_a_7663_, v_a_7664_, v_a_7665_, v_a_7666_, v_a_7667_, v_a_7668_,
        );
        return v___x_7673_;
    } else {
        return v___x_7672_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed(
    mut v_stx_7674_: *mut LeanObject,
    mut v_a_7675_: *mut LeanObject,
    mut v_a_7676_: *mut LeanObject,
    mut v_a_7677_: *mut LeanObject,
    mut v_a_7678_: *mut LeanObject,
    mut v_a_7679_: *mut LeanObject,
    mut v_a_7680_: *mut LeanObject,
    mut v_a_7681_: *mut LeanObject,
    mut v_a_7682_: *mut LeanObject,
    mut v_a_7683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7684_: *mut LeanObject = core::ptr::null_mut();
    v_res_7684_ = l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(
        v_stx_7674_,
        v_a_7675_,
        v_a_7676_,
        v_a_7677_,
        v_a_7678_,
        v_a_7679_,
        v_a_7680_,
        v_a_7681_,
        v_a_7682_,
    );
    lean_dec(v_a_7682_);
    lean_dec_ref(v_a_7681_);
    lean_dec(v_a_7680_);
    lean_dec_ref(v_a_7679_);
    lean_dec(v_a_7678_);
    lean_dec_ref(v_a_7677_);
    lean_dec(v_a_7676_);
    lean_dec_ref(v_a_7675_);
    lean_dec(v_stx_7674_);
    return v_res_7684_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1()
-> *mut LeanObject {
    let mut v___x_7700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7704_: *mut LeanObject = core::ptr::null_mut();
    v___x_7700_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7701_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1;
    v___x_7702_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3;
    v___x_7703_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7704_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7700_,
        v___x_7701_,
        v___x_7702_,
        v___x_7703_,
    );
    return v___x_7704_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___boxed(
    mut v_a_7705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7706_: *mut LeanObject = core::ptr::null_mut();
    v_res_7706_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
    return v_res_7706_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3()
-> *mut LeanObject {
    let mut v___x_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7735_: *mut LeanObject = core::ptr::null_mut();
    v___x_7733_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3;
    v___x_7734_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6;
    v___x_7735_ = l_Lean_addBuiltinDeclarationRanges(v___x_7733_, v___x_7734_);
    return v___x_7735_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___boxed(
    mut v_a_7736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7737_: *mut LeanObject = core::ptr::null_mut();
    v_res_7737_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
    return v_res_7737_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(
    mut v_seq_7738_: *mut LeanObject,
    mut v___y_7739_: *mut LeanObject,
    mut v___y_7740_: *mut LeanObject,
    mut v___y_7741_: *mut LeanObject,
    mut v___y_7742_: *mut LeanObject,
    mut v___y_7743_: *mut LeanObject,
    mut v___y_7744_: *mut LeanObject,
    mut v___y_7745_: *mut LeanObject,
    mut v___y_7746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7748_: *mut LeanObject = core::ptr::null_mut();
    v___x_7748_ = l_Lean_Elab_Tactic_evalTactic(
        v_seq_7738_,
        v___y_7739_,
        v___y_7740_,
        v___y_7741_,
        v___y_7742_,
        v___y_7743_,
        v___y_7744_,
        v___y_7745_,
        v___y_7746_,
    );
    if lean_obj_tag(v___x_7748_) == 0 {
        let mut v___x_7749_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_7748_, 1);
        v___x_7749_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(
            v___y_7739_,
            v___y_7740_,
            v___y_7741_,
            v___y_7742_,
            v___y_7743_,
            v___y_7744_,
            v___y_7745_,
            v___y_7746_,
        );
        return v___x_7749_;
    } else {
        return v___x_7748_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed(
    mut v_seq_7750_: *mut LeanObject,
    mut v___y_7751_: *mut LeanObject,
    mut v___y_7752_: *mut LeanObject,
    mut v___y_7753_: *mut LeanObject,
    mut v___y_7754_: *mut LeanObject,
    mut v___y_7755_: *mut LeanObject,
    mut v___y_7756_: *mut LeanObject,
    mut v___y_7757_: *mut LeanObject,
    mut v___y_7758_: *mut LeanObject,
    mut v___y_7759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7760_: *mut LeanObject = core::ptr::null_mut();
    v_res_7760_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(
        v_seq_7750_,
        v___y_7751_,
        v___y_7752_,
        v___y_7753_,
        v___y_7754_,
        v___y_7755_,
        v___y_7756_,
        v___y_7757_,
        v___y_7758_,
    );
    lean_dec(v___y_7758_);
    lean_dec_ref(v___y_7757_);
    lean_dec(v___y_7756_);
    lean_dec_ref(v___y_7755_);
    lean_dec(v___y_7754_);
    lean_dec_ref(v___y_7753_);
    lean_dec(v___y_7752_);
    lean_dec_ref(v___y_7751_);
    return v_res_7760_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(
    mut v_a_7761_: *mut LeanObject,
    mut v___y_7762_: *mut LeanObject,
    mut v___y_7763_: *mut LeanObject,
    mut v___y_7764_: *mut LeanObject,
    mut v___y_7765_: *mut LeanObject,
    mut v___y_7766_: *mut LeanObject,
    mut v___y_7767_: *mut LeanObject,
    mut v___y_7768_: *mut LeanObject,
    mut v___y_7769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7782_: u8 = 0;
    let mut v___x_7784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7786_: u8 = 0;
    let mut v_a_7787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7790_: u8 = 0;
    let mut v___x_7792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7771_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_7763_,
                    v___y_7766_,
                    v___y_7767_,
                    v___y_7768_,
                    v___y_7769_,
                );
                if lean_obj_tag(v___x_7771_) == 0 {
                    v_a_7772_ = lean_ctor_get(v___x_7771_, 0);
                    lean_inc(v_a_7772_);
                    lean_dec_ref_known(v___x_7771_, 1);
                    v___x_7773_ = l_Lean_Expr_mdataExpr_x21(v_a_7761_);
                    v___x_7774_ = l_Lean_MVarId_replaceTargetDefEq(
                        v_a_7772_,
                        v___x_7773_,
                        v___y_7766_,
                        v___y_7767_,
                        v___y_7768_,
                        v___y_7769_,
                    );
                    if lean_obj_tag(v___x_7774_) == 0 {
                        v_a_7775_ = lean_ctor_get(v___x_7774_, 0);
                        lean_inc(v_a_7775_);
                        lean_dec_ref_known(v___x_7774_, 1);
                        v___x_7776_ = lean_box(0);
                        v___x_7777_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_7777_, 0, v_a_7775_);
                        lean_ctor_set(v___x_7777_, 1, v___x_7776_);
                        v___x_7778_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_7777_,
                            v___y_7763_,
                            v___y_7766_,
                            v___y_7767_,
                            v___y_7768_,
                            v___y_7769_,
                        );
                        return v___x_7778_;
                    } else {
                        v_a_7779_ = lean_ctor_get(v___x_7774_, 0);
                        v_isSharedCheck_7786_ = (!lean_is_exclusive(v___x_7774_)) as u8;
                        if v_isSharedCheck_7786_ == 0 {
                            v___x_7781_ = v___x_7774_;
                            v_isShared_7782_ = v_isSharedCheck_7786_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7779_);
                            lean_dec(v___x_7774_);
                            v___x_7781_ = lean_box(0);
                            v_isShared_7782_ = v_isSharedCheck_7786_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_7787_ = lean_ctor_get(v___x_7771_, 0);
                    v_isSharedCheck_7794_ = (!lean_is_exclusive(v___x_7771_)) as u8;
                    if v_isSharedCheck_7794_ == 0 {
                        v___x_7789_ = v___x_7771_;
                        v_isShared_7790_ = v_isSharedCheck_7794_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7787_);
                        lean_dec(v___x_7771_);
                        v___x_7789_ = lean_box(0);
                        v_isShared_7790_ = v_isSharedCheck_7794_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7782_ == 0 {
                    v___x_7784_ = v___x_7781_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7785_, 0, v_a_7779_);
                    v___x_7784_ = v_reuseFailAlloc_7785_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7784_;
            }
            3 => {
                if v_isShared_7790_ == 0 {
                    v___x_7792_ = v___x_7789_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7793_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7793_, 0, v_a_7787_);
                    v___x_7792_ = v_reuseFailAlloc_7793_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed(
    mut v_a_7795_: *mut LeanObject,
    mut v___y_7796_: *mut LeanObject,
    mut v___y_7797_: *mut LeanObject,
    mut v___y_7798_: *mut LeanObject,
    mut v___y_7799_: *mut LeanObject,
    mut v___y_7800_: *mut LeanObject,
    mut v___y_7801_: *mut LeanObject,
    mut v___y_7802_: *mut LeanObject,
    mut v___y_7803_: *mut LeanObject,
    mut v___y_7804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7805_: *mut LeanObject = core::ptr::null_mut();
    v_res_7805_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(
        v_a_7795_,
        v___y_7796_,
        v___y_7797_,
        v___y_7798_,
        v___y_7799_,
        v___y_7800_,
        v___y_7801_,
        v___y_7802_,
        v___y_7803_,
    );
    lean_dec(v___y_7803_);
    lean_dec_ref(v___y_7802_);
    lean_dec(v___y_7801_);
    lean_dec_ref(v___y_7800_);
    lean_dec(v___y_7799_);
    lean_dec_ref(v___y_7798_);
    lean_dec(v___y_7797_);
    lean_dec_ref(v___y_7796_);
    lean_dec_ref(v_a_7795_);
    return v_res_7805_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalNestedTactic(
    mut v_stx_7806_: *mut LeanObject,
    mut v_a_7807_: *mut LeanObject,
    mut v_a_7808_: *mut LeanObject,
    mut v_a_7809_: *mut LeanObject,
    mut v_a_7810_: *mut LeanObject,
    mut v_a_7811_: *mut LeanObject,
    mut v_a_7812_: *mut LeanObject,
    mut v_a_7813_: *mut LeanObject,
    mut v_a_7814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seq_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7829_: u8 = 0;
    let mut v___x_7831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7833_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7816_ = l_Lean_Elab_Tactic_getMainTarget(
                    v_a_7807_, v_a_7808_, v_a_7809_, v_a_7810_, v_a_7811_, v_a_7812_, v_a_7813_,
                    v_a_7814_,
                );
                if lean_obj_tag(v___x_7816_) == 0 {
                    v_a_7817_ = lean_ctor_get(v___x_7816_, 0);
                    lean_inc(v_a_7817_);
                    lean_dec_ref_known(v___x_7816_, 1);
                    v___x_7818_ = lean_unsigned_to_nat(2);
                    v_seq_7819_ = l_Lean_Syntax_getArg(v_stx_7806_, v___x_7818_);
                    v___f_7820_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_7820_, 0, v_seq_7819_);
                    v___x_7821_ = l_Lean_isLHSGoal_x3f(v_a_7817_);
                    if lean_obj_tag(v___x_7821_) == 1 {
                        lean_dec_ref_known(v___x_7821_, 1);
                        v___f_7822_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed
                                as *mut core::ffi::c_void,
                            10,
                            1,
                        );
                        lean_closure_set(v___f_7822_, 0, v_a_7817_);
                        v___x_7823_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                            v___f_7822_,
                            v_a_7807_,
                            v_a_7808_,
                            v_a_7809_,
                            v_a_7810_,
                            v_a_7811_,
                            v_a_7812_,
                            v_a_7813_,
                            v_a_7814_,
                        );
                        if lean_obj_tag(v___x_7823_) == 0 {
                            lean_dec_ref_known(v___x_7823_, 1);
                            v___x_7824_ = l_Lean_Elab_Tactic_focus___redArg(
                                v___f_7820_,
                                v_a_7807_,
                                v_a_7808_,
                                v_a_7809_,
                                v_a_7810_,
                                v_a_7811_,
                                v_a_7812_,
                                v_a_7813_,
                                v_a_7814_,
                            );
                            return v___x_7824_;
                        } else {
                            lean_dec_ref(v___f_7820_);
                            return v___x_7823_;
                        }
                    } else {
                        lean_dec(v___x_7821_);
                        lean_dec(v_a_7817_);
                        v___x_7825_ = l_Lean_Elab_Tactic_focus___redArg(
                            v___f_7820_,
                            v_a_7807_,
                            v_a_7808_,
                            v_a_7809_,
                            v_a_7810_,
                            v_a_7811_,
                            v_a_7812_,
                            v_a_7813_,
                            v_a_7814_,
                        );
                        return v___x_7825_;
                    }
                } else {
                    v_a_7826_ = lean_ctor_get(v___x_7816_, 0);
                    v_isSharedCheck_7833_ = (!lean_is_exclusive(v___x_7816_)) as u8;
                    if v_isSharedCheck_7833_ == 0 {
                        v___x_7828_ = v___x_7816_;
                        v_isShared_7829_ = v_isSharedCheck_7833_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7826_);
                        lean_dec(v___x_7816_);
                        v___x_7828_ = lean_box(0);
                        v_isShared_7829_ = v_isSharedCheck_7833_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7829_ == 0 {
                    v___x_7831_ = v___x_7828_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7832_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7832_, 0, v_a_7826_);
                    v___x_7831_ = v_reuseFailAlloc_7832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed(
    mut v_stx_7834_: *mut LeanObject,
    mut v_a_7835_: *mut LeanObject,
    mut v_a_7836_: *mut LeanObject,
    mut v_a_7837_: *mut LeanObject,
    mut v_a_7838_: *mut LeanObject,
    mut v_a_7839_: *mut LeanObject,
    mut v_a_7840_: *mut LeanObject,
    mut v_a_7841_: *mut LeanObject,
    mut v_a_7842_: *mut LeanObject,
    mut v_a_7843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7844_: *mut LeanObject = core::ptr::null_mut();
    v_res_7844_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic(
        v_stx_7834_,
        v_a_7835_,
        v_a_7836_,
        v_a_7837_,
        v_a_7838_,
        v_a_7839_,
        v_a_7840_,
        v_a_7841_,
        v_a_7842_,
    );
    lean_dec(v_a_7842_);
    lean_dec_ref(v_a_7841_);
    lean_dec(v_a_7840_);
    lean_dec_ref(v_a_7839_);
    lean_dec(v_a_7838_);
    lean_dec_ref(v_a_7837_);
    lean_dec(v_a_7836_);
    lean_dec_ref(v_a_7835_);
    lean_dec(v_stx_7834_);
    return v_res_7844_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1()
-> *mut LeanObject {
    let mut v___x_7860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    v___x_7860_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7861_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1;
    v___x_7862_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3;
    v___x_7863_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7864_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7860_,
        v___x_7861_,
        v___x_7862_,
        v___x_7863_,
    );
    return v___x_7864_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___boxed(
    mut v_a_7865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7866_: *mut LeanObject = core::ptr::null_mut();
    v_res_7866_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
    return v_res_7866_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3()
-> *mut LeanObject {
    let mut v___x_7893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7895_: *mut LeanObject = core::ptr::null_mut();
    v___x_7893_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3;
    v___x_7894_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6;
    v___x_7895_ = l_Lean_addBuiltinDeclarationRanges(v___x_7893_, v___x_7894_);
    return v___x_7895_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___boxed(
    mut v_a_7896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7897_: *mut LeanObject = core::ptr::null_mut();
    v_res_7897_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
    return v_res_7897_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvTactic(
    mut v_stx_7898_: *mut LeanObject,
    mut v_a_7899_: *mut LeanObject,
    mut v_a_7900_: *mut LeanObject,
    mut v_a_7901_: *mut LeanObject,
    mut v_a_7902_: *mut LeanObject,
    mut v_a_7903_: *mut LeanObject,
    mut v_a_7904_: *mut LeanObject,
    mut v_a_7905_: *mut LeanObject,
    mut v_a_7906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7910_: *mut LeanObject = core::ptr::null_mut();
    v___x_7908_ = lean_unsigned_to_nat(2);
    v___x_7909_ = l_Lean_Syntax_getArg(v_stx_7898_, v___x_7908_);
    v___x_7910_ = l_Lean_Elab_Tactic_evalTactic(
        v___x_7909_,
        v_a_7899_,
        v_a_7900_,
        v_a_7901_,
        v_a_7902_,
        v_a_7903_,
        v_a_7904_,
        v_a_7905_,
        v_a_7906_,
    );
    return v___x_7910_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed(
    mut v_stx_7911_: *mut LeanObject,
    mut v_a_7912_: *mut LeanObject,
    mut v_a_7913_: *mut LeanObject,
    mut v_a_7914_: *mut LeanObject,
    mut v_a_7915_: *mut LeanObject,
    mut v_a_7916_: *mut LeanObject,
    mut v_a_7917_: *mut LeanObject,
    mut v_a_7918_: *mut LeanObject,
    mut v_a_7919_: *mut LeanObject,
    mut v_a_7920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7921_: *mut LeanObject = core::ptr::null_mut();
    v_res_7921_ = l_Lean_Elab_Tactic_Conv_evalConvTactic(
        v_stx_7911_,
        v_a_7912_,
        v_a_7913_,
        v_a_7914_,
        v_a_7915_,
        v_a_7916_,
        v_a_7917_,
        v_a_7918_,
        v_a_7919_,
    );
    lean_dec(v_a_7919_);
    lean_dec_ref(v_a_7918_);
    lean_dec(v_a_7917_);
    lean_dec_ref(v_a_7916_);
    lean_dec(v_a_7915_);
    lean_dec_ref(v_a_7914_);
    lean_dec(v_a_7913_);
    lean_dec_ref(v_a_7912_);
    lean_dec(v_stx_7911_);
    return v_res_7921_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1()
-> *mut LeanObject {
    let mut v___x_7937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7941_: *mut LeanObject = core::ptr::null_mut();
    v___x_7937_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7938_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1;
    v___x_7939_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3;
    v___x_7940_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7941_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7937_,
        v___x_7938_,
        v___x_7939_,
        v___x_7940_,
    );
    return v___x_7941_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___boxed(
    mut v_a_7942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7943_: *mut LeanObject = core::ptr::null_mut();
    v_res_7943_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
    return v_res_7943_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3()
-> *mut LeanObject {
    let mut v___x_7970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7972_: *mut LeanObject = core::ptr::null_mut();
    v___x_7970_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3;
    v___x_7971_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6;
    v___x_7972_ = l_Lean_addBuiltinDeclarationRanges(v___x_7970_, v___x_7971_);
    return v___x_7972_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___boxed(
    mut v_a_7973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7974_: *mut LeanObject = core::ptr::null_mut();
    v_res_7974_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
    return v_res_7974_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(
    mut v_ref_7975_: *mut LeanObject,
    mut v___x_7976_: *mut LeanObject,
    mut v___y_7977_: *mut LeanObject,
    mut v___y_7978_: *mut LeanObject,
    mut v___y_7979_: *mut LeanObject,
    mut v___y_7980_: *mut LeanObject,
    mut v___y_7981_: *mut LeanObject,
    mut v___y_7982_: *mut LeanObject,
    mut v___y_7983_: *mut LeanObject,
    mut v___y_7984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7993_: u8 = 0;
    let mut v___x_7995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7986_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(
                    v_ref_7975_,
                    v___y_7977_,
                    v___y_7978_,
                    v___y_7979_,
                    v___y_7980_,
                    v___y_7981_,
                    v___y_7982_,
                    v___y_7983_,
                    v___y_7984_,
                );
                if lean_obj_tag(v___x_7986_) == 0 {
                    v_a_7987_ = lean_ctor_get(v___x_7986_, 0);
                    lean_inc(v_a_7987_);
                    lean_dec_ref_known(v___x_7986_, 1);
                    v___f_7988_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    lean_closure_set(v___f_7988_, 0, v_a_7987_);
                    v___x_7989_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v___x_7976_, v___f_7988_, v___y_7977_, v___y_7978_, v___y_7979_, v___y_7980_, v___y_7981_, v___y_7982_, v___y_7983_, v___y_7984_);
                    return v___x_7989_;
                } else {
                    lean_dec_ref(v___x_7976_);
                    v_a_7990_ = lean_ctor_get(v___x_7986_, 0);
                    v_isSharedCheck_7997_ = (!lean_is_exclusive(v___x_7986_)) as u8;
                    if v_isSharedCheck_7997_ == 0 {
                        v___x_7992_ = v___x_7986_;
                        v_isShared_7993_ = v_isSharedCheck_7997_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7990_);
                        lean_dec(v___x_7986_);
                        v___x_7992_ = lean_box(0);
                        v_isShared_7993_ = v_isSharedCheck_7997_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7993_ == 0 {
                    v___x_7995_ = v___x_7992_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7996_, 0, v_a_7990_);
                    v___x_7995_ = v_reuseFailAlloc_7996_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed(
    mut v_ref_7998_: *mut LeanObject,
    mut v___x_7999_: *mut LeanObject,
    mut v___y_8000_: *mut LeanObject,
    mut v___y_8001_: *mut LeanObject,
    mut v___y_8002_: *mut LeanObject,
    mut v___y_8003_: *mut LeanObject,
    mut v___y_8004_: *mut LeanObject,
    mut v___y_8005_: *mut LeanObject,
    mut v___y_8006_: *mut LeanObject,
    mut v___y_8007_: *mut LeanObject,
    mut v___y_8008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8009_: *mut LeanObject = core::ptr::null_mut();
    v_res_8009_ =
        l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(
            v_ref_7998_,
            v___x_7999_,
            v___y_8000_,
            v___y_8001_,
            v___y_8002_,
            v___y_8003_,
            v___y_8004_,
            v___y_8005_,
            v___y_8006_,
            v___y_8007_,
        );
    lean_dec(v___y_8007_);
    lean_dec_ref(v___y_8006_);
    lean_dec(v___y_8005_);
    lean_dec_ref(v___y_8004_);
    lean_dec(v___y_8003_);
    lean_dec_ref(v___y_8002_);
    lean_dec(v___y_8001_);
    lean_dec_ref(v___y_8000_);
    return v_res_8009_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(
    mut v_fst_8010_: *mut LeanObject,
    mut v_snd_8011_: *mut LeanObject,
    mut v___y_8012_: *mut LeanObject,
    mut v___y_8013_: *mut LeanObject,
    mut v___y_8014_: *mut LeanObject,
    mut v___y_8015_: *mut LeanObject,
    mut v___y_8016_: *mut LeanObject,
    mut v___y_8017_: *mut LeanObject,
    mut v___y_8018_: *mut LeanObject,
    mut v___y_8019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8031_: u8 = 0;
    let mut v___x_8033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8035_: u8 = 0;
    let mut v_a_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8039_: u8 = 0;
    let mut v___x_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8021_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_8013_,
                    v___y_8016_,
                    v___y_8017_,
                    v___y_8018_,
                    v___y_8019_,
                );
                if lean_obj_tag(v___x_8021_) == 0 {
                    v_a_8022_ = lean_ctor_get(v___x_8021_, 0);
                    lean_inc(v_a_8022_);
                    lean_dec_ref_known(v___x_8021_, 1);
                    v___x_8023_ = l_Lean_MVarId_replaceTargetEq(
                        v_a_8022_,
                        v_fst_8010_,
                        v_snd_8011_,
                        v___y_8016_,
                        v___y_8017_,
                        v___y_8018_,
                        v___y_8019_,
                    );
                    if lean_obj_tag(v___x_8023_) == 0 {
                        v_a_8024_ = lean_ctor_get(v___x_8023_, 0);
                        lean_inc(v_a_8024_);
                        lean_dec_ref_known(v___x_8023_, 1);
                        v___x_8025_ = lean_box(0);
                        v___x_8026_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_8026_, 0, v_a_8024_);
                        lean_ctor_set(v___x_8026_, 1, v___x_8025_);
                        v___x_8027_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_8026_,
                            v___y_8013_,
                            v___y_8016_,
                            v___y_8017_,
                            v___y_8018_,
                            v___y_8019_,
                        );
                        return v___x_8027_;
                    } else {
                        v_a_8028_ = lean_ctor_get(v___x_8023_, 0);
                        v_isSharedCheck_8035_ = (!lean_is_exclusive(v___x_8023_)) as u8;
                        if v_isSharedCheck_8035_ == 0 {
                            v___x_8030_ = v___x_8023_;
                            v_isShared_8031_ = v_isSharedCheck_8035_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8028_);
                            lean_dec(v___x_8023_);
                            v___x_8030_ = lean_box(0);
                            v_isShared_8031_ = v_isSharedCheck_8035_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_snd_8011_);
                    lean_dec_ref(v_fst_8010_);
                    v_a_8036_ = lean_ctor_get(v___x_8021_, 0);
                    v_isSharedCheck_8043_ = (!lean_is_exclusive(v___x_8021_)) as u8;
                    if v_isSharedCheck_8043_ == 0 {
                        v___x_8038_ = v___x_8021_;
                        v_isShared_8039_ = v_isSharedCheck_8043_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8036_);
                        lean_dec(v___x_8021_);
                        v___x_8038_ = lean_box(0);
                        v_isShared_8039_ = v_isSharedCheck_8043_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8031_ == 0 {
                    v___x_8033_ = v___x_8030_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8034_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8034_, 0, v_a_8028_);
                    v___x_8033_ = v_reuseFailAlloc_8034_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8033_;
            }
            3 => {
                if v_isShared_8039_ == 0 {
                    v___x_8041_ = v___x_8038_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8042_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8042_, 0, v_a_8036_);
                    v___x_8041_ = v_reuseFailAlloc_8042_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed(
    mut v_fst_8044_: *mut LeanObject,
    mut v_snd_8045_: *mut LeanObject,
    mut v___y_8046_: *mut LeanObject,
    mut v___y_8047_: *mut LeanObject,
    mut v___y_8048_: *mut LeanObject,
    mut v___y_8049_: *mut LeanObject,
    mut v___y_8050_: *mut LeanObject,
    mut v___y_8051_: *mut LeanObject,
    mut v___y_8052_: *mut LeanObject,
    mut v___y_8053_: *mut LeanObject,
    mut v___y_8054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8055_: *mut LeanObject = core::ptr::null_mut();
    v_res_8055_ =
        l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(
            v_fst_8044_,
            v_snd_8045_,
            v___y_8046_,
            v___y_8047_,
            v___y_8048_,
            v___y_8049_,
            v___y_8050_,
            v___y_8051_,
            v___y_8052_,
            v___y_8053_,
        );
    lean_dec(v___y_8053_);
    lean_dec_ref(v___y_8052_);
    lean_dec(v___y_8051_);
    lean_dec_ref(v___y_8050_);
    lean_dec(v___y_8049_);
    lean_dec_ref(v___y_8048_);
    lean_dec(v___y_8047_);
    lean_dec_ref(v___y_8046_);
    return v_res_8055_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(
    mut v_conv_8056_: *mut LeanObject,
    mut v___y_8057_: *mut LeanObject,
    mut v___y_8058_: *mut LeanObject,
    mut v___y_8059_: *mut LeanObject,
    mut v___y_8060_: *mut LeanObject,
    mut v___y_8061_: *mut LeanObject,
    mut v___y_8062_: *mut LeanObject,
    mut v___y_8063_: *mut LeanObject,
    mut v___y_8064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8077_: u8 = 0;
    let mut v___f_8078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8080_: u8 = 0;
    let mut v___x_8081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8106_: u8 = 0;
    let mut v_a_8107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8110_: u8 = 0;
    let mut v___x_8112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8114_: u8 = 0;
    let mut v_a_8115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8118_: u8 = 0;
    let mut v___x_8120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8066_ = l_Lean_Elab_Tactic_getMainTarget(
                    v___y_8057_,
                    v___y_8058_,
                    v___y_8059_,
                    v___y_8060_,
                    v___y_8061_,
                    v___y_8062_,
                    v___y_8063_,
                    v___y_8064_,
                );
                if lean_obj_tag(v___x_8066_) == 0 {
                    v_a_8067_ = lean_ctor_get(v___x_8066_, 0);
                    lean_inc(v_a_8067_);
                    lean_dec_ref_known(v___x_8066_, 1);
                    v_ref_8068_ = lean_ctor_get(v___y_8063_, 5);
                    v___x_8069_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalTactic___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___x_8069_, 0, v_conv_8056_);
                    lean_inc(v_ref_8068_);
                    v___f_8070_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed as *mut core::ffi::c_void, 11, 2);
                    lean_closure_set(v___f_8070_, 0, v_ref_8068_);
                    lean_closure_set(v___f_8070_, 1, v___x_8069_);
                    v___x_8071_ = l_Lean_Elab_Tactic_Conv_convert(
                        v_a_8067_,
                        v___f_8070_,
                        v___y_8057_,
                        v___y_8058_,
                        v___y_8059_,
                        v___y_8060_,
                        v___y_8061_,
                        v___y_8062_,
                        v___y_8063_,
                        v___y_8064_,
                    );
                    if lean_obj_tag(v___x_8071_) == 0 {
                        v_a_8072_ = lean_ctor_get(v___x_8071_, 0);
                        lean_inc(v_a_8072_);
                        lean_dec_ref_known(v___x_8071_, 1);
                        v_fst_8073_ = lean_ctor_get(v_a_8072_, 0);
                        v_snd_8074_ = lean_ctor_get(v_a_8072_, 1);
                        v_isSharedCheck_8106_ = (!lean_is_exclusive(v_a_8072_)) as u8;
                        if v_isSharedCheck_8106_ == 0 {
                            v___x_8076_ = v_a_8072_;
                            v_isShared_8077_ = v_isSharedCheck_8106_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_8074_);
                            lean_inc(v_fst_8073_);
                            lean_dec(v_a_8072_);
                            v___x_8076_ = lean_box(0);
                            v_isShared_8077_ = v_isSharedCheck_8106_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___y_8063_);
                        v_a_8107_ = lean_ctor_get(v___x_8071_, 0);
                        v_isSharedCheck_8114_ = (!lean_is_exclusive(v___x_8071_)) as u8;
                        if v_isSharedCheck_8114_ == 0 {
                            v___x_8109_ = v___x_8071_;
                            v_isShared_8110_ = v_isSharedCheck_8114_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_8107_);
                            lean_dec(v___x_8071_);
                            v___x_8109_ = lean_box(0);
                            v_isShared_8110_ = v_isSharedCheck_8114_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_8063_);
                    lean_dec(v_conv_8056_);
                    v_a_8115_ = lean_ctor_get(v___x_8066_, 0);
                    v_isSharedCheck_8122_ = (!lean_is_exclusive(v___x_8066_)) as u8;
                    if v_isSharedCheck_8122_ == 0 {
                        v___x_8117_ = v___x_8066_;
                        v_isShared_8118_ = v_isSharedCheck_8122_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_8115_);
                        lean_dec(v___x_8066_);
                        v___x_8117_ = lean_box(0);
                        v_isShared_8118_ = v_isSharedCheck_8122_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___f_8078_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
                lean_closure_set(v___f_8078_, 0, v_fst_8073_);
                lean_closure_set(v___f_8078_, 1, v_snd_8074_);
                v___x_8079_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___f_8078_,
                    v___y_8057_,
                    v___y_8058_,
                    v___y_8059_,
                    v___y_8060_,
                    v___y_8061_,
                    v___y_8062_,
                    v___y_8063_,
                    v___y_8064_,
                );
                if lean_obj_tag(v___x_8079_) == 0 {
                    lean_dec_ref_known(v___x_8079_, 1);
                    v___x_8080_ = 0;
                    v___x_8081_ = l_Lean_SourceInfo_fromRef(v_ref_8068_, v___x_8080_);
                    v___x_8082_ =
                        l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13;
                    v___x_8083_ =
                        l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14;
                    lean_inc(v___x_8081_);
                    if v_isShared_8077_ == 0 {
                        lean_ctor_set_tag(v___x_8076_, 2);
                        lean_ctor_set(v___x_8076_, 1, v___x_8083_);
                        lean_ctor_set(v___x_8076_, 0, v___x_8081_);
                        v___x_8085_ = v___x_8076_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8105_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8105_, 0, v___x_8081_);
                        lean_ctor_set(v_reuseFailAlloc_8105_, 1, v___x_8083_);
                        v___x_8085_ = v_reuseFailAlloc_8105_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8076_);
                    lean_dec_ref(v___y_8063_);
                    return v___x_8079_;
                }
            }
            2 => {
                v___x_8086_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4;
                v___x_8087_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6;
                v___x_8088_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8;
                v___x_8089_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16;
                v___x_8090_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17;
                lean_inc_n(v___x_8081_, 10);
                v___x_8091_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8091_, 0, v___x_8081_);
                lean_ctor_set(v___x_8091_, 1, v___x_8090_);
                v___x_8092_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19;
                v___x_8093_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20;
                v___x_8094_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8094_, 0, v___x_8081_);
                lean_ctor_set(v___x_8094_, 1, v___x_8093_);
                v___x_8095_ = l_Lean_Syntax_node1(v___x_8081_, v___x_8092_, v___x_8094_);
                v___x_8096_ = l_Lean_Syntax_node1(v___x_8081_, v___x_8088_, v___x_8095_);
                v___x_8097_ = l_Lean_Syntax_node1(v___x_8081_, v___x_8087_, v___x_8096_);
                v___x_8098_ = l_Lean_Syntax_node1(v___x_8081_, v___x_8086_, v___x_8097_);
                v___x_8099_ =
                    l_Lean_Syntax_node2(v___x_8081_, v___x_8089_, v___x_8091_, v___x_8098_);
                v___x_8100_ = l_Lean_Syntax_node1(v___x_8081_, v___x_8088_, v___x_8099_);
                v___x_8101_ = l_Lean_Syntax_node1(v___x_8081_, v___x_8087_, v___x_8100_);
                v___x_8102_ = l_Lean_Syntax_node1(v___x_8081_, v___x_8086_, v___x_8101_);
                v___x_8103_ =
                    l_Lean_Syntax_node2(v___x_8081_, v___x_8082_, v___x_8085_, v___x_8102_);
                v___x_8104_ = l_Lean_Elab_Tactic_evalTactic(
                    v___x_8103_,
                    v___y_8057_,
                    v___y_8058_,
                    v___y_8059_,
                    v___y_8060_,
                    v___y_8061_,
                    v___y_8062_,
                    v___y_8063_,
                    v___y_8064_,
                );
                lean_dec_ref(v___y_8063_);
                return v___x_8104_;
            }
            3 => {
                if v_isShared_8110_ == 0 {
                    v___x_8112_ = v___x_8109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8113_, 0, v_a_8107_);
                    v___x_8112_ = v_reuseFailAlloc_8113_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8112_;
            }
            5 => {
                if v_isShared_8118_ == 0 {
                    v___x_8120_ = v___x_8117_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8121_, 0, v_a_8115_);
                    v___x_8120_ = v_reuseFailAlloc_8121_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed(
    mut v_conv_8123_: *mut LeanObject,
    mut v___y_8124_: *mut LeanObject,
    mut v___y_8125_: *mut LeanObject,
    mut v___y_8126_: *mut LeanObject,
    mut v___y_8127_: *mut LeanObject,
    mut v___y_8128_: *mut LeanObject,
    mut v___y_8129_: *mut LeanObject,
    mut v___y_8130_: *mut LeanObject,
    mut v___y_8131_: *mut LeanObject,
    mut v___y_8132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8133_: *mut LeanObject = core::ptr::null_mut();
    v_res_8133_ =
        l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(
            v_conv_8123_,
            v___y_8124_,
            v___y_8125_,
            v___y_8126_,
            v___y_8127_,
            v___y_8128_,
            v___y_8129_,
            v___y_8130_,
            v___y_8131_,
        );
    lean_dec(v___y_8131_);
    lean_dec(v___y_8129_);
    lean_dec_ref(v___y_8128_);
    lean_dec(v___y_8127_);
    lean_dec_ref(v___y_8126_);
    lean_dec(v___y_8125_);
    lean_dec_ref(v___y_8124_);
    return v_res_8133_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(
    mut v_conv_8134_: *mut LeanObject,
    mut v_a_8135_: *mut LeanObject,
    mut v_a_8136_: *mut LeanObject,
    mut v_a_8137_: *mut LeanObject,
    mut v_a_8138_: *mut LeanObject,
    mut v_a_8139_: *mut LeanObject,
    mut v_a_8140_: *mut LeanObject,
    mut v_a_8141_: *mut LeanObject,
    mut v_a_8142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut LeanObject = core::ptr::null_mut();
    v___f_8144_ = lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed
            as *mut core::ffi::c_void,
        10,
        1,
    );
    lean_closure_set(v___f_8144_, 0, v_conv_8134_);
    v___x_8145_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_8144_,
        v_a_8135_,
        v_a_8136_,
        v_a_8137_,
        v_a_8138_,
        v_a_8139_,
        v_a_8140_,
        v_a_8141_,
        v_a_8142_,
    );
    return v___x_8145_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___boxed(
    mut v_conv_8146_: *mut LeanObject,
    mut v_a_8147_: *mut LeanObject,
    mut v_a_8148_: *mut LeanObject,
    mut v_a_8149_: *mut LeanObject,
    mut v_a_8150_: *mut LeanObject,
    mut v_a_8151_: *mut LeanObject,
    mut v_a_8152_: *mut LeanObject,
    mut v_a_8153_: *mut LeanObject,
    mut v_a_8154_: *mut LeanObject,
    mut v_a_8155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8156_: *mut LeanObject = core::ptr::null_mut();
    v_res_8156_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(
        v_conv_8146_,
        v_a_8147_,
        v_a_8148_,
        v_a_8149_,
        v_a_8150_,
        v_a_8151_,
        v_a_8152_,
        v_a_8153_,
        v_a_8154_,
    );
    lean_dec(v_a_8154_);
    lean_dec_ref(v_a_8153_);
    lean_dec(v_a_8152_);
    lean_dec_ref(v_a_8151_);
    lean_dec(v_a_8150_);
    lean_dec_ref(v_a_8149_);
    lean_dec(v_a_8148_);
    lean_dec_ref(v_a_8147_);
    return v_res_8156_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(
    mut v_snd_8157_: *mut LeanObject,
    mut v___x_8158_: *mut LeanObject,
    mut v_fst_8159_: *mut LeanObject,
    mut v_a_8160_: *mut LeanObject,
    mut v___x_8161_: *mut LeanObject,
    mut v___y_8162_: *mut LeanObject,
    mut v___y_8163_: *mut LeanObject,
    mut v___y_8164_: *mut LeanObject,
    mut v___y_8165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8175_: u8 = 0;
    let mut v___x_8177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8167_ = l_Lean_Meta_mkEqMP(
                    v_snd_8157_,
                    v___x_8158_,
                    v___y_8162_,
                    v___y_8163_,
                    v___y_8164_,
                    v___y_8165_,
                );
                if lean_obj_tag(v___x_8167_) == 0 {
                    v_a_8168_ = lean_ctor_get(v___x_8167_, 0);
                    lean_inc(v_a_8168_);
                    lean_dec_ref_known(v___x_8167_, 1);
                    v___x_8169_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8169_, 0, v_fst_8159_);
                    v___x_8170_ = lean_box(0);
                    v___x_8171_ = l_Lean_MVarId_replace(
                        v_a_8160_,
                        v___x_8161_,
                        v_a_8168_,
                        v___x_8169_,
                        v___x_8170_,
                        v___y_8162_,
                        v___y_8163_,
                        v___y_8164_,
                        v___y_8165_,
                    );
                    return v___x_8171_;
                } else {
                    lean_dec(v___x_8161_);
                    lean_dec(v_a_8160_);
                    lean_dec_ref(v_fst_8159_);
                    v_a_8172_ = lean_ctor_get(v___x_8167_, 0);
                    v_isSharedCheck_8179_ = (!lean_is_exclusive(v___x_8167_)) as u8;
                    if v_isSharedCheck_8179_ == 0 {
                        v___x_8174_ = v___x_8167_;
                        v_isShared_8175_ = v_isSharedCheck_8179_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8172_);
                        lean_dec(v___x_8167_);
                        v___x_8174_ = lean_box(0);
                        v_isShared_8175_ = v_isSharedCheck_8179_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8175_ == 0 {
                    v___x_8177_ = v___x_8174_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8178_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8178_, 0, v_a_8172_);
                    v___x_8177_ = v_reuseFailAlloc_8178_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed(
    mut v_snd_8180_: *mut LeanObject,
    mut v___x_8181_: *mut LeanObject,
    mut v_fst_8182_: *mut LeanObject,
    mut v_a_8183_: *mut LeanObject,
    mut v___x_8184_: *mut LeanObject,
    mut v___y_8185_: *mut LeanObject,
    mut v___y_8186_: *mut LeanObject,
    mut v___y_8187_: *mut LeanObject,
    mut v___y_8188_: *mut LeanObject,
    mut v___y_8189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8190_: *mut LeanObject = core::ptr::null_mut();
    v_res_8190_ =
        l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(
            v_snd_8180_,
            v___x_8181_,
            v_fst_8182_,
            v_a_8183_,
            v___x_8184_,
            v___y_8185_,
            v___y_8186_,
            v___y_8187_,
            v___y_8188_,
        );
    lean_dec(v___y_8188_);
    lean_dec_ref(v___y_8187_);
    lean_dec(v___y_8186_);
    lean_dec_ref(v___y_8185_);
    return v_res_8190_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(
    mut v_a_8191_: *mut LeanObject,
    mut v_snd_8192_: *mut LeanObject,
    mut v_fst_8193_: *mut LeanObject,
    mut v___y_8194_: *mut LeanObject,
    mut v___y_8195_: *mut LeanObject,
    mut v___y_8196_: *mut LeanObject,
    mut v___y_8197_: *mut LeanObject,
    mut v___y_8198_: *mut LeanObject,
    mut v___y_8199_: *mut LeanObject,
    mut v___y_8200_: *mut LeanObject,
    mut v___y_8201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_8210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8217_: u8 = 0;
    let mut v___x_8219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8221_: u8 = 0;
    let mut v_a_8222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8225_: u8 = 0;
    let mut v___x_8227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8203_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_8195_,
                    v___y_8198_,
                    v___y_8199_,
                    v___y_8200_,
                    v___y_8201_,
                );
                if lean_obj_tag(v___x_8203_) == 0 {
                    v_a_8204_ = lean_ctor_get(v___x_8203_, 0);
                    lean_inc_n(v_a_8204_, 2);
                    lean_dec_ref_known(v___x_8203_, 1);
                    v___x_8205_ = l_Lean_LocalDecl_fvarId(v_a_8191_);
                    lean_inc(v___x_8205_);
                    v___x_8206_ = l_Lean_mkFVar(v___x_8205_);
                    v___f_8207_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed as *mut core::ffi::c_void, 10, 5);
                    lean_closure_set(v___f_8207_, 0, v_snd_8192_);
                    lean_closure_set(v___f_8207_, 1, v___x_8206_);
                    lean_closure_set(v___f_8207_, 2, v_fst_8193_);
                    lean_closure_set(v___f_8207_, 3, v_a_8204_);
                    lean_closure_set(v___f_8207_, 4, v___x_8205_);
                    v___x_8208_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_a_8204_, v___f_8207_, v___y_8198_, v___y_8199_, v___y_8200_, v___y_8201_);
                    if lean_obj_tag(v___x_8208_) == 0 {
                        v_a_8209_ = lean_ctor_get(v___x_8208_, 0);
                        lean_inc(v_a_8209_);
                        lean_dec_ref_known(v___x_8208_, 1);
                        v_mvarId_8210_ = lean_ctor_get(v_a_8209_, 1);
                        lean_inc(v_mvarId_8210_);
                        lean_dec(v_a_8209_);
                        v___x_8211_ = lean_box(0);
                        v___x_8212_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_8212_, 0, v_mvarId_8210_);
                        lean_ctor_set(v___x_8212_, 1, v___x_8211_);
                        v___x_8213_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_8212_,
                            v___y_8195_,
                            v___y_8198_,
                            v___y_8199_,
                            v___y_8200_,
                            v___y_8201_,
                        );
                        return v___x_8213_;
                    } else {
                        v_a_8214_ = lean_ctor_get(v___x_8208_, 0);
                        v_isSharedCheck_8221_ = (!lean_is_exclusive(v___x_8208_)) as u8;
                        if v_isSharedCheck_8221_ == 0 {
                            v___x_8216_ = v___x_8208_;
                            v_isShared_8217_ = v_isSharedCheck_8221_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8214_);
                            lean_dec(v___x_8208_);
                            v___x_8216_ = lean_box(0);
                            v_isShared_8217_ = v_isSharedCheck_8221_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_fst_8193_);
                    lean_dec_ref(v_snd_8192_);
                    v_a_8222_ = lean_ctor_get(v___x_8203_, 0);
                    v_isSharedCheck_8229_ = (!lean_is_exclusive(v___x_8203_)) as u8;
                    if v_isSharedCheck_8229_ == 0 {
                        v___x_8224_ = v___x_8203_;
                        v_isShared_8225_ = v_isSharedCheck_8229_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8222_);
                        lean_dec(v___x_8203_);
                        v___x_8224_ = lean_box(0);
                        v_isShared_8225_ = v_isSharedCheck_8229_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8217_ == 0 {
                    v___x_8219_ = v___x_8216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8220_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8220_, 0, v_a_8214_);
                    v___x_8219_ = v_reuseFailAlloc_8220_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8219_;
            }
            3 => {
                if v_isShared_8225_ == 0 {
                    v___x_8227_ = v___x_8224_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8228_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8228_, 0, v_a_8222_);
                    v___x_8227_ = v_reuseFailAlloc_8228_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed(
    mut v_a_8230_: *mut LeanObject,
    mut v_snd_8231_: *mut LeanObject,
    mut v_fst_8232_: *mut LeanObject,
    mut v___y_8233_: *mut LeanObject,
    mut v___y_8234_: *mut LeanObject,
    mut v___y_8235_: *mut LeanObject,
    mut v___y_8236_: *mut LeanObject,
    mut v___y_8237_: *mut LeanObject,
    mut v___y_8238_: *mut LeanObject,
    mut v___y_8239_: *mut LeanObject,
    mut v___y_8240_: *mut LeanObject,
    mut v___y_8241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8242_: *mut LeanObject = core::ptr::null_mut();
    v_res_8242_ =
        l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(
            v_a_8230_,
            v_snd_8231_,
            v_fst_8232_,
            v___y_8233_,
            v___y_8234_,
            v___y_8235_,
            v___y_8236_,
            v___y_8237_,
            v___y_8238_,
            v___y_8239_,
            v___y_8240_,
        );
    lean_dec(v___y_8240_);
    lean_dec_ref(v___y_8239_);
    lean_dec(v___y_8238_);
    lean_dec_ref(v___y_8237_);
    lean_dec(v___y_8236_);
    lean_dec_ref(v___y_8235_);
    lean_dec(v___y_8234_);
    lean_dec_ref(v___y_8233_);
    lean_dec_ref(v_a_8230_);
    return v_res_8242_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1(
    mut v_hUserName_8243_: *mut LeanObject,
    mut v_conv_8244_: *mut LeanObject,
    mut v___y_8245_: *mut LeanObject,
    mut v___y_8246_: *mut LeanObject,
    mut v___y_8247_: *mut LeanObject,
    mut v___y_8248_: *mut LeanObject,
    mut v___y_8249_: *mut LeanObject,
    mut v___y_8250_: *mut LeanObject,
    mut v___y_8251_: *mut LeanObject,
    mut v___y_8252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8269_: u8 = 0;
    let mut v___x_8271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8273_: u8 = 0;
    let mut v_a_8274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8277_: u8 = 0;
    let mut v___x_8279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8254_ = l_Lean_Meta_getLocalDeclFromUserName(
                    v_hUserName_8243_,
                    v___y_8249_,
                    v___y_8250_,
                    v___y_8251_,
                    v___y_8252_,
                );
                if lean_obj_tag(v___x_8254_) == 0 {
                    v_a_8255_ = lean_ctor_get(v___x_8254_, 0);
                    lean_inc(v_a_8255_);
                    lean_dec_ref_known(v___x_8254_, 1);
                    v_ref_8256_ = lean_ctor_get(v___y_8251_, 5);
                    v___x_8257_ = l_Lean_LocalDecl_type(v_a_8255_);
                    v___x_8258_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalTactic___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___x_8258_, 0, v_conv_8244_);
                    lean_inc(v_ref_8256_);
                    v___f_8259_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed as *mut core::ffi::c_void, 11, 2);
                    lean_closure_set(v___f_8259_, 0, v_ref_8256_);
                    lean_closure_set(v___f_8259_, 1, v___x_8258_);
                    v___x_8260_ = l_Lean_Elab_Tactic_Conv_convert(
                        v___x_8257_,
                        v___f_8259_,
                        v___y_8245_,
                        v___y_8246_,
                        v___y_8247_,
                        v___y_8248_,
                        v___y_8249_,
                        v___y_8250_,
                        v___y_8251_,
                        v___y_8252_,
                    );
                    if lean_obj_tag(v___x_8260_) == 0 {
                        v_a_8261_ = lean_ctor_get(v___x_8260_, 0);
                        lean_inc(v_a_8261_);
                        lean_dec_ref_known(v___x_8260_, 1);
                        v_fst_8262_ = lean_ctor_get(v_a_8261_, 0);
                        lean_inc(v_fst_8262_);
                        v_snd_8263_ = lean_ctor_get(v_a_8261_, 1);
                        lean_inc(v_snd_8263_);
                        lean_dec(v_a_8261_);
                        v___f_8264_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed as *mut core::ffi::c_void, 12, 3);
                        lean_closure_set(v___f_8264_, 0, v_a_8255_);
                        lean_closure_set(v___f_8264_, 1, v_snd_8263_);
                        lean_closure_set(v___f_8264_, 2, v_fst_8262_);
                        v___x_8265_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                            v___f_8264_,
                            v___y_8245_,
                            v___y_8246_,
                            v___y_8247_,
                            v___y_8248_,
                            v___y_8249_,
                            v___y_8250_,
                            v___y_8251_,
                            v___y_8252_,
                        );
                        lean_dec_ref(v___y_8251_);
                        return v___x_8265_;
                    } else {
                        lean_dec(v_a_8255_);
                        lean_dec_ref(v___y_8251_);
                        v_a_8266_ = lean_ctor_get(v___x_8260_, 0);
                        v_isSharedCheck_8273_ = (!lean_is_exclusive(v___x_8260_)) as u8;
                        if v_isSharedCheck_8273_ == 0 {
                            v___x_8268_ = v___x_8260_;
                            v_isShared_8269_ = v_isSharedCheck_8273_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8266_);
                            lean_dec(v___x_8260_);
                            v___x_8268_ = lean_box(0);
                            v_isShared_8269_ = v_isSharedCheck_8273_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_8251_);
                    lean_dec(v_conv_8244_);
                    v_a_8274_ = lean_ctor_get(v___x_8254_, 0);
                    v_isSharedCheck_8281_ = (!lean_is_exclusive(v___x_8254_)) as u8;
                    if v_isSharedCheck_8281_ == 0 {
                        v___x_8276_ = v___x_8254_;
                        v_isShared_8277_ = v_isSharedCheck_8281_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8274_);
                        lean_dec(v___x_8254_);
                        v___x_8276_ = lean_box(0);
                        v_isShared_8277_ = v_isSharedCheck_8281_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8269_ == 0 {
                    v___x_8271_ = v___x_8268_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8272_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8272_, 0, v_a_8266_);
                    v___x_8271_ = v_reuseFailAlloc_8272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8271_;
            }
            3 => {
                if v_isShared_8277_ == 0 {
                    v___x_8279_ = v___x_8276_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8280_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8280_, 0, v_a_8274_);
                    v___x_8279_ = v_reuseFailAlloc_8280_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1___boxed(
    mut v_hUserName_8282_: *mut LeanObject,
    mut v_conv_8283_: *mut LeanObject,
    mut v___y_8284_: *mut LeanObject,
    mut v___y_8285_: *mut LeanObject,
    mut v___y_8286_: *mut LeanObject,
    mut v___y_8287_: *mut LeanObject,
    mut v___y_8288_: *mut LeanObject,
    mut v___y_8289_: *mut LeanObject,
    mut v___y_8290_: *mut LeanObject,
    mut v___y_8291_: *mut LeanObject,
    mut v___y_8292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8293_: *mut LeanObject = core::ptr::null_mut();
    v_res_8293_ =
        l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1(
            v_hUserName_8282_,
            v_conv_8283_,
            v___y_8284_,
            v___y_8285_,
            v___y_8286_,
            v___y_8287_,
            v___y_8288_,
            v___y_8289_,
            v___y_8290_,
            v___y_8291_,
        );
    lean_dec(v___y_8291_);
    lean_dec(v___y_8289_);
    lean_dec_ref(v___y_8288_);
    lean_dec(v___y_8287_);
    lean_dec_ref(v___y_8286_);
    lean_dec(v___y_8285_);
    lean_dec_ref(v___y_8284_);
    return v_res_8293_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(
    mut v_conv_8294_: *mut LeanObject,
    mut v_hUserName_8295_: *mut LeanObject,
    mut v_a_8296_: *mut LeanObject,
    mut v_a_8297_: *mut LeanObject,
    mut v_a_8298_: *mut LeanObject,
    mut v_a_8299_: *mut LeanObject,
    mut v_a_8300_: *mut LeanObject,
    mut v_a_8301_: *mut LeanObject,
    mut v_a_8302_: *mut LeanObject,
    mut v_a_8303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8306_: *mut LeanObject = core::ptr::null_mut();
    v___f_8305_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1___boxed as *mut core::ffi::c_void, 11, 2);
    lean_closure_set(v___f_8305_, 0, v_hUserName_8295_);
    lean_closure_set(v___f_8305_, 1, v_conv_8294_);
    v___x_8306_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_8305_,
        v_a_8296_,
        v_a_8297_,
        v_a_8298_,
        v_a_8299_,
        v_a_8300_,
        v_a_8301_,
        v_a_8302_,
        v_a_8303_,
    );
    return v___x_8306_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___boxed(
    mut v_conv_8307_: *mut LeanObject,
    mut v_hUserName_8308_: *mut LeanObject,
    mut v_a_8309_: *mut LeanObject,
    mut v_a_8310_: *mut LeanObject,
    mut v_a_8311_: *mut LeanObject,
    mut v_a_8312_: *mut LeanObject,
    mut v_a_8313_: *mut LeanObject,
    mut v_a_8314_: *mut LeanObject,
    mut v_a_8315_: *mut LeanObject,
    mut v_a_8316_: *mut LeanObject,
    mut v_a_8317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8318_: *mut LeanObject = core::ptr::null_mut();
    v_res_8318_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(
        v_conv_8307_,
        v_hUserName_8308_,
        v_a_8309_,
        v_a_8310_,
        v_a_8311_,
        v_a_8312_,
        v_a_8313_,
        v_a_8314_,
        v_a_8315_,
        v_a_8316_,
    );
    lean_dec(v_a_8316_);
    lean_dec_ref(v_a_8315_);
    lean_dec(v_a_8314_);
    lean_dec_ref(v_a_8313_);
    lean_dec(v_a_8312_);
    lean_dec_ref(v_a_8311_);
    lean_dec(v_a_8310_);
    lean_dec_ref(v_a_8309_);
    return v_res_8318_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__7() -> *mut LeanObject {
    let mut v___x_8337_: *mut LeanObject = core::ptr::null_mut();
    v___x_8337_ = l_Array_mkArray0(lean_box(0));
    return v___x_8337_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConv(
    mut v_stx_8339_: *mut LeanObject,
    mut v_a_8340_: *mut LeanObject,
    mut v_a_8341_: *mut LeanObject,
    mut v_a_8342_: *mut LeanObject,
    mut v_a_8343_: *mut LeanObject,
    mut v_a_8344_: *mut LeanObject,
    mut v_a_8345_: *mut LeanObject,
    mut v_a_8346_: *mut LeanObject,
    mut v_a_8347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8390_: u8 = 0;
    let mut v___x_8391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_8426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8443_: u8 = 0;
    let mut v___x_8444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_loc_x3f_8456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8468_: u8 = 0;
    let mut v___x_8469_: u8 = 0;
    let mut v___x_8470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_8471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_8472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_8475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_8477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_8478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_8479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_8480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_8481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_8482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_8483_: u8 = 0;
    let mut v_cancelTk_x3f_8484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_8485_: u8 = 0;
    let mut v_inheritedTraceOptions_8486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arr_8487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arr_8504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8513_: u8 = 0;
    let mut v___x_8515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8517_: u8 = 0;
    let mut v___x_8518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8519_: u8 = 0;
    let mut v___x_8520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8521_: u8 = 0;
    let mut v___x_8522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_loc_x3f_8523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8525_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8349_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__0;
                v___x_8350_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__1;
                lean_inc(v_stx_8339_);
                v___x_8390_ = l_Lean_Syntax_isOfKind(v_stx_8339_, v___x_8350_);
                if v___x_8390_ == 0 {
                    lean_dec(v_stx_8339_);
                    v___x_8391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
                    return v___x_8391_;
                } else {
                    v___x_8392_ = lean_unsigned_to_nat(0);
                    v_tk_8426_ = l_Lean_Syntax_getArg(v_stx_8339_, v___x_8392_);
                    v___x_8454_ = lean_unsigned_to_nat(1);
                    v___x_8518_ = l_Lean_Syntax_getArg(v_stx_8339_, v___x_8454_);
                    v___x_8519_ = l_Lean_Syntax_isNone(v___x_8518_);
                    if v___x_8519_ == 0 {
                        v___x_8520_ = lean_unsigned_to_nat(2);
                        lean_inc(v___x_8518_);
                        v___x_8521_ = l_Lean_Syntax_matchesNull(v___x_8518_, v___x_8520_);
                        if v___x_8521_ == 0 {
                            lean_dec(v___x_8518_);
                            lean_dec(v_tk_8426_);
                            lean_dec(v_stx_8339_);
                            v___x_8522_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
                            return v___x_8522_;
                        } else {
                            v_loc_x3f_8523_ = l_Lean_Syntax_getArg(v___x_8518_, v___x_8454_);
                            lean_dec(v___x_8518_);
                            v___x_8524_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_8524_, 0, v_loc_x3f_8523_);
                            v_loc_x3f_8456_ = v___x_8524_;
                            v___y_8457_ = v_a_8340_;
                            v___y_8458_ = v_a_8341_;
                            v___y_8459_ = v_a_8342_;
                            v___y_8460_ = v_a_8343_;
                            v___y_8461_ = v_a_8344_;
                            v___y_8462_ = v_a_8345_;
                            v___y_8463_ = v_a_8346_;
                            v___y_8464_ = v_a_8347_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_8518_);
                        v___x_8525_ = lean_box(0);
                        v_loc_x3f_8456_ = v___x_8525_;
                        v___y_8457_ = v_a_8340_;
                        v___y_8458_ = v_a_8341_;
                        v___y_8459_ = v_a_8342_;
                        v___y_8460_ = v_a_8343_;
                        v___y_8461_ = v_a_8344_;
                        v___y_8462_ = v_a_8345_;
                        v___y_8463_ = v_a_8346_;
                        v___y_8464_ = v_a_8347_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_8353_);
                v___x_8374_ = l_Array_append___redArg(v___y_8353_, v___y_8373_);
                lean_dec_ref(v___y_8373_);
                lean_inc_n(v___y_8356_, 2);
                lean_inc_n(v___y_8358_, 9);
                v___x_8375_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8375_, 0, v___y_8358_);
                lean_ctor_set(v___x_8375_, 1, v___y_8356_);
                lean_ctor_set(v___x_8375_, 2, v___x_8374_);
                lean_inc(v___y_8369_);
                v___x_8376_ = l_Lean_Syntax_node3(
                    v___y_8358_,
                    v___y_8369_,
                    v___y_8370_,
                    v___x_8375_,
                    v___y_8360_,
                );
                v___x_8377_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__2;
                v___x_8378_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8378_, 0, v___y_8358_);
                lean_ctor_set(v___x_8378_, 1, v___x_8377_);
                v___x_8379_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0;
                v___x_8380_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11;
                v___x_8381_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8381_, 0, v___y_8358_);
                lean_ctor_set(v___x_8381_, 1, v___x_8380_);
                v___x_8382_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21;
                v___x_8383_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8383_, 0, v___y_8358_);
                lean_ctor_set(v___x_8383_, 1, v___x_8382_);
                v___x_8384_ = l_Lean_Syntax_node3(
                    v___y_8358_,
                    v___x_8379_,
                    v___x_8381_,
                    v___y_8365_,
                    v___x_8383_,
                );
                v___x_8385_ = l_Lean_Syntax_node3(
                    v___y_8358_,
                    v___y_8356_,
                    v___x_8376_,
                    v___x_8378_,
                    v___x_8384_,
                );
                lean_inc(v___y_8355_);
                v___x_8386_ = l_Lean_Syntax_node1(v___y_8358_, v___y_8355_, v___x_8385_);
                lean_inc(v___y_8361_);
                v___x_8387_ = l_Lean_Syntax_node1(v___y_8358_, v___y_8361_, v___x_8386_);
                v___x_8388_ = l_Lean_Syntax_node5(
                    v___y_8358_,
                    v___x_8350_,
                    v___y_8354_,
                    v___y_8371_,
                    v___y_8357_,
                    v___y_8366_,
                    v___x_8387_,
                );
                v___x_8389_ = l_Lean_Elab_Tactic_evalTactic(
                    v___x_8388_,
                    v___y_8364_,
                    v___y_8372_,
                    v___y_8368_,
                    v___y_8367_,
                    v___y_8359_,
                    v___y_8352_,
                    v___y_8362_,
                    v___y_8363_,
                );
                return v___x_8389_;
            }
            2 => {
                lean_inc_ref_n(v___y_8394_, 2);
                v___x_8412_ = l_Array_append___redArg(v___y_8394_, v___y_8411_);
                lean_dec_ref(v___y_8411_);
                lean_inc_n(v___y_8397_, 2);
                lean_inc_n(v___y_8398_, 3);
                v___x_8413_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8413_, 0, v___y_8398_);
                lean_ctor_set(v___x_8413_, 1, v___y_8397_);
                lean_ctor_set(v___x_8413_, 2, v___x_8412_);
                v___x_8414_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8414_, 0, v___y_8398_);
                lean_ctor_set(v___x_8414_, 1, v___y_8397_);
                lean_ctor_set(v___x_8414_, 2, v___y_8394_);
                v___x_8415_ = l_Lean_SourceInfo_fromRef(v___y_8410_, v___x_8390_);
                lean_dec(v___y_8410_);
                v___x_8416_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__3;
                v___x_8417_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8417_, 0, v___x_8415_);
                lean_ctor_set(v___x_8417_, 1, v___x_8416_);
                v___x_8418_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1;
                v___x_8419_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__4;
                v___x_8420_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__5;
                v___x_8421_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8421_, 0, v___y_8398_);
                lean_ctor_set(v___x_8421_, 1, v___x_8419_);
                if lean_obj_tag(v___y_8399_) == 0 {
                    v___x_8422_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__6;
                    v___y_8352_ = v___y_8395_;
                    v___y_8353_ = v___y_8394_;
                    v___y_8354_ = v___y_8396_;
                    v___y_8355_ = v___x_8418_;
                    v___y_8356_ = v___y_8397_;
                    v___y_8357_ = v___x_8414_;
                    v___y_8358_ = v___y_8398_;
                    v___y_8359_ = v___y_8400_;
                    v___y_8360_ = v___y_8401_;
                    v___y_8361_ = v___y_8402_;
                    v___y_8362_ = v___y_8403_;
                    v___y_8363_ = v___y_8404_;
                    v___y_8364_ = v___y_8405_;
                    v___y_8365_ = v___y_8406_;
                    v___y_8366_ = v___x_8417_;
                    v___y_8367_ = v___y_8408_;
                    v___y_8368_ = v___y_8407_;
                    v___y_8369_ = v___x_8420_;
                    v___y_8370_ = v___x_8421_;
                    v___y_8371_ = v___x_8413_;
                    v___y_8372_ = v___y_8409_;
                    v___y_8373_ = v___x_8422_;
                    state = 1;
                    continue;
                } else {
                    v_val_8423_ = lean_ctor_get(v___y_8399_, 0);
                    lean_inc(v_val_8423_);
                    lean_dec_ref_known(v___y_8399_, 1);
                    v___x_8424_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__6;
                    v___x_8425_ = lean_array_push(v___x_8424_, v_val_8423_);
                    v___y_8352_ = v___y_8395_;
                    v___y_8353_ = v___y_8394_;
                    v___y_8354_ = v___y_8396_;
                    v___y_8355_ = v___x_8418_;
                    v___y_8356_ = v___y_8397_;
                    v___y_8357_ = v___x_8414_;
                    v___y_8358_ = v___y_8398_;
                    v___y_8359_ = v___y_8400_;
                    v___y_8360_ = v___y_8401_;
                    v___y_8361_ = v___y_8402_;
                    v___y_8362_ = v___y_8403_;
                    v___y_8363_ = v___y_8404_;
                    v___y_8364_ = v___y_8405_;
                    v___y_8365_ = v___y_8406_;
                    v___y_8366_ = v___x_8417_;
                    v___y_8367_ = v___y_8408_;
                    v___y_8368_ = v___y_8407_;
                    v___y_8369_ = v___x_8420_;
                    v___y_8370_ = v___x_8421_;
                    v___y_8371_ = v___x_8413_;
                    v___y_8372_ = v___y_8409_;
                    v___y_8373_ = v___x_8425_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_ref_8442_ = lean_ctor_get(v___y_8432_, 5);
                v___x_8443_ = 0;
                v___x_8444_ = l_Lean_SourceInfo_fromRef(v_ref_8442_, v___x_8443_);
                v___x_8445_ = l_Lean_SourceInfo_fromRef(v_tk_8426_, v___x_8390_);
                lean_dec(v_tk_8426_);
                v___x_8446_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8446_, 0, v___x_8445_);
                lean_ctor_set(v___x_8446_, 1, v___x_8349_);
                v___x_8447_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8;
                v___x_8448_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalConv___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalConv___closed__7_once),
                    _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__7,
                );
                if lean_obj_tag(v___y_8438_) == 1 {
                    v_val_8449_ = lean_ctor_get(v___y_8438_, 0);
                    lean_inc(v_val_8449_);
                    lean_dec_ref_known(v___y_8438_, 1);
                    v___x_8450_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__8;
                    lean_inc(v___x_8444_);
                    v___x_8451_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_8451_, 0, v___x_8444_);
                    lean_ctor_set(v___x_8451_, 1, v___x_8450_);
                    v___x_8452_ = l_Array_mkArray2___redArg(v___x_8451_, v_val_8449_);
                    v___y_8394_ = v___x_8448_;
                    v___y_8395_ = v___y_8428_;
                    v___y_8396_ = v___x_8446_;
                    v___y_8397_ = v___x_8447_;
                    v___y_8398_ = v___x_8444_;
                    v___y_8399_ = v___y_8441_;
                    v___y_8400_ = v___y_8429_;
                    v___y_8401_ = v___y_8430_;
                    v___y_8402_ = v___y_8431_;
                    v___y_8403_ = v___y_8432_;
                    v___y_8404_ = v___y_8433_;
                    v___y_8405_ = v___y_8434_;
                    v___y_8406_ = v___y_8435_;
                    v___y_8407_ = v___y_8436_;
                    v___y_8408_ = v___y_8437_;
                    v___y_8409_ = v___y_8439_;
                    v___y_8410_ = v___y_8440_;
                    v___y_8411_ = v___x_8452_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_8438_);
                    v___x_8453_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__6;
                    v___y_8394_ = v___x_8448_;
                    v___y_8395_ = v___y_8428_;
                    v___y_8396_ = v___x_8446_;
                    v___y_8397_ = v___x_8447_;
                    v___y_8398_ = v___x_8444_;
                    v___y_8399_ = v___y_8441_;
                    v___y_8400_ = v___y_8429_;
                    v___y_8401_ = v___y_8430_;
                    v___y_8402_ = v___y_8431_;
                    v___y_8403_ = v___y_8432_;
                    v___y_8404_ = v___y_8433_;
                    v___y_8405_ = v___y_8434_;
                    v___y_8406_ = v___y_8435_;
                    v___y_8407_ = v___y_8436_;
                    v___y_8408_ = v___y_8437_;
                    v___y_8409_ = v___y_8439_;
                    v___y_8410_ = v___y_8440_;
                    v___y_8411_ = v___x_8453_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_8465_ = lean_unsigned_to_nat(2);
                v___x_8466_ = l_Lean_Syntax_getArg(v_stx_8339_, v___x_8465_);
                v___x_8467_ = lean_unsigned_to_nat(3);
                lean_inc(v___x_8466_);
                v___x_8468_ = l_Lean_Syntax_matchesNull(v___x_8466_, v___x_8467_);
                if v___x_8468_ == 0 {
                    v___x_8469_ = l_Lean_Syntax_matchesNull(v___x_8466_, v___x_8392_);
                    if v___x_8469_ == 0 {
                        lean_dec(v_loc_x3f_8456_);
                        lean_dec(v_tk_8426_);
                        lean_dec(v_stx_8339_);
                        v___x_8470_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
                        return v___x_8470_;
                    } else {
                        v_fileName_8471_ = lean_ctor_get(v___y_8463_, 0);
                        v_fileMap_8472_ = lean_ctor_get(v___y_8463_, 1);
                        v_options_8473_ = lean_ctor_get(v___y_8463_, 2);
                        v_currRecDepth_8474_ = lean_ctor_get(v___y_8463_, 3);
                        v_maxRecDepth_8475_ = lean_ctor_get(v___y_8463_, 4);
                        v_ref_8476_ = lean_ctor_get(v___y_8463_, 5);
                        v_currNamespace_8477_ = lean_ctor_get(v___y_8463_, 6);
                        v_openDecls_8478_ = lean_ctor_get(v___y_8463_, 7);
                        v_initHeartbeats_8479_ = lean_ctor_get(v___y_8463_, 8);
                        v_maxHeartbeats_8480_ = lean_ctor_get(v___y_8463_, 9);
                        v_quotContext_8481_ = lean_ctor_get(v___y_8463_, 10);
                        v_currMacroScope_8482_ = lean_ctor_get(v___y_8463_, 11);
                        v_diag_8483_ = lean_ctor_get_uint8(
                            v___y_8463_,
                            (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        );
                        v_cancelTk_x3f_8484_ = lean_ctor_get(v___y_8463_, 12);
                        v_suppressElabErrors_8485_ = lean_ctor_get_uint8(
                            v___y_8463_,
                            (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        );
                        v_inheritedTraceOptions_8486_ = lean_ctor_get(v___y_8463_, 13);
                        v_arr_8487_ = l_Lean_Syntax_getArg(v_stx_8339_, v___x_8467_);
                        v___x_8488_ = lean_unsigned_to_nat(4);
                        v___x_8489_ = l_Lean_Syntax_getArg(v_stx_8339_, v___x_8488_);
                        lean_dec(v_stx_8339_);
                        v___x_8490_ = lean_mk_empty_array_with_capacity(v___x_8465_);
                        v___x_8491_ = lean_array_push(v___x_8490_, v_tk_8426_);
                        v___x_8492_ = lean_array_push(v___x_8491_, v_arr_8487_);
                        v___x_8493_ =
                            l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8;
                        v___x_8494_ = lean_box(2);
                        v___x_8495_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_8495_, 0, v___x_8494_);
                        lean_ctor_set(v___x_8495_, 1, v___x_8493_);
                        lean_ctor_set(v___x_8495_, 2, v___x_8492_);
                        v_ref_8496_ = l_Lean_replaceRef(v___x_8495_, v_ref_8476_);
                        lean_dec_ref_known(v___x_8495_, 3);
                        lean_inc_ref(v_inheritedTraceOptions_8486_);
                        lean_inc(v_cancelTk_x3f_8484_);
                        lean_inc(v_currMacroScope_8482_);
                        lean_inc(v_quotContext_8481_);
                        lean_inc(v_maxHeartbeats_8480_);
                        lean_inc(v_initHeartbeats_8479_);
                        lean_inc(v_openDecls_8478_);
                        lean_inc(v_currNamespace_8477_);
                        lean_inc(v_maxRecDepth_8475_);
                        lean_inc(v_currRecDepth_8474_);
                        lean_inc_ref(v_options_8473_);
                        lean_inc_ref(v_fileMap_8472_);
                        lean_inc_ref(v_fileName_8471_);
                        v___x_8497_ = lean_alloc_ctor(0, 14, (2) as u32);
                        lean_ctor_set(v___x_8497_, 0, v_fileName_8471_);
                        lean_ctor_set(v___x_8497_, 1, v_fileMap_8472_);
                        lean_ctor_set(v___x_8497_, 2, v_options_8473_);
                        lean_ctor_set(v___x_8497_, 3, v_currRecDepth_8474_);
                        lean_ctor_set(v___x_8497_, 4, v_maxRecDepth_8475_);
                        lean_ctor_set(v___x_8497_, 5, v_ref_8496_);
                        lean_ctor_set(v___x_8497_, 6, v_currNamespace_8477_);
                        lean_ctor_set(v___x_8497_, 7, v_openDecls_8478_);
                        lean_ctor_set(v___x_8497_, 8, v_initHeartbeats_8479_);
                        lean_ctor_set(v___x_8497_, 9, v_maxHeartbeats_8480_);
                        lean_ctor_set(v___x_8497_, 10, v_quotContext_8481_);
                        lean_ctor_set(v___x_8497_, 11, v_currMacroScope_8482_);
                        lean_ctor_set(v___x_8497_, 12, v_cancelTk_x3f_8484_);
                        lean_ctor_set(v___x_8497_, 13, v_inheritedTraceOptions_8486_);
                        lean_ctor_set_uint8(
                            v___x_8497_,
                            (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                            v_diag_8483_,
                        );
                        lean_ctor_set_uint8(
                            v___x_8497_,
                            (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                            v_suppressElabErrors_8485_,
                        );
                        if lean_obj_tag(v_loc_x3f_8456_) == 1 {
                            v_val_8498_ = lean_ctor_get(v_loc_x3f_8456_, 0);
                            lean_inc(v_val_8498_);
                            lean_dec_ref_known(v_loc_x3f_8456_, 1);
                            v___x_8499_ = l_Lean_TSyntax_getId(v_val_8498_);
                            lean_dec(v_val_8498_);
                            v___x_8500_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(v___x_8489_, v___x_8499_, v___y_8457_, v___y_8458_, v___y_8459_, v___y_8460_, v___y_8461_, v___y_8462_, v___x_8497_, v___y_8464_);
                            lean_dec_ref_known(v___x_8497_, 14);
                            return v___x_8500_;
                        } else {
                            lean_dec(v_loc_x3f_8456_);
                            v___x_8501_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(v___x_8489_, v___y_8457_, v___y_8458_, v___y_8459_, v___y_8460_, v___y_8461_, v___y_8462_, v___x_8497_, v___y_8464_);
                            lean_dec_ref_known(v___x_8497_, 14);
                            return v___x_8501_;
                        }
                    }
                } else {
                    v___x_8502_ = l_Lean_Syntax_getArg(v___x_8466_, v___x_8454_);
                    v___x_8503_ = l_Lean_Syntax_getArg(v___x_8466_, v___x_8465_);
                    lean_dec(v___x_8466_);
                    v_arr_8504_ = l_Lean_Syntax_getArg(v_stx_8339_, v___x_8467_);
                    v___x_8505_ = lean_unsigned_to_nat(4);
                    v___x_8506_ = l_Lean_Syntax_getArg(v_stx_8339_, v___x_8505_);
                    lean_dec(v_stx_8339_);
                    v___x_8507_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1;
                    v___x_8508_ = l_Lean_Syntax_getOptional_x3f(v___x_8502_);
                    lean_dec(v___x_8502_);
                    if lean_obj_tag(v___x_8508_) == 0 {
                        v___x_8509_ = lean_box(0);
                        v___y_8428_ = v___y_8462_;
                        v___y_8429_ = v___y_8461_;
                        v___y_8430_ = v___x_8503_;
                        v___y_8431_ = v___x_8507_;
                        v___y_8432_ = v___y_8463_;
                        v___y_8433_ = v___y_8464_;
                        v___y_8434_ = v___y_8457_;
                        v___y_8435_ = v___x_8506_;
                        v___y_8436_ = v___y_8459_;
                        v___y_8437_ = v___y_8460_;
                        v___y_8438_ = v_loc_x3f_8456_;
                        v___y_8439_ = v___y_8458_;
                        v___y_8440_ = v_arr_8504_;
                        v___y_8441_ = v___x_8509_;
                        state = 3;
                        continue;
                    } else {
                        v_val_8510_ = lean_ctor_get(v___x_8508_, 0);
                        v_isSharedCheck_8517_ = (!lean_is_exclusive(v___x_8508_)) as u8;
                        if v_isSharedCheck_8517_ == 0 {
                            v___x_8512_ = v___x_8508_;
                            v_isShared_8513_ = v_isSharedCheck_8517_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_val_8510_);
                            lean_dec(v___x_8508_);
                            v___x_8512_ = lean_box(0);
                            v_isShared_8513_ = v_isSharedCheck_8517_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_8513_ == 0 {
                    v___x_8515_ = v___x_8512_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8516_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8516_, 0, v_val_8510_);
                    v___x_8515_ = v_reuseFailAlloc_8516_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_8428_ = v___y_8462_;
                v___y_8429_ = v___y_8461_;
                v___y_8430_ = v___x_8503_;
                v___y_8431_ = v___x_8507_;
                v___y_8432_ = v___y_8463_;
                v___y_8433_ = v___y_8464_;
                v___y_8434_ = v___y_8457_;
                v___y_8435_ = v___x_8506_;
                v___y_8436_ = v___y_8459_;
                v___y_8437_ = v___y_8460_;
                v___y_8438_ = v_loc_x3f_8456_;
                v___y_8439_ = v___y_8458_;
                v___y_8440_ = v_arr_8504_;
                v___y_8441_ = v___x_8515_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalConv___boxed(
    mut v_stx_8526_: *mut LeanObject,
    mut v_a_8527_: *mut LeanObject,
    mut v_a_8528_: *mut LeanObject,
    mut v_a_8529_: *mut LeanObject,
    mut v_a_8530_: *mut LeanObject,
    mut v_a_8531_: *mut LeanObject,
    mut v_a_8532_: *mut LeanObject,
    mut v_a_8533_: *mut LeanObject,
    mut v_a_8534_: *mut LeanObject,
    mut v_a_8535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8536_: *mut LeanObject = core::ptr::null_mut();
    v_res_8536_ = l_Lean_Elab_Tactic_Conv_evalConv(
        v_stx_8526_,
        v_a_8527_,
        v_a_8528_,
        v_a_8529_,
        v_a_8530_,
        v_a_8531_,
        v_a_8532_,
        v_a_8533_,
        v_a_8534_,
    );
    lean_dec(v_a_8534_);
    lean_dec_ref(v_a_8533_);
    lean_dec(v_a_8532_);
    lean_dec_ref(v_a_8531_);
    lean_dec(v_a_8530_);
    lean_dec_ref(v_a_8529_);
    lean_dec(v_a_8528_);
    lean_dec_ref(v_a_8527_);
    return v_res_8536_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1()
-> *mut LeanObject {
    let mut v___x_8545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8549_: *mut LeanObject = core::ptr::null_mut();
    v___x_8545_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_8546_ = l_Lean_Elab_Tactic_Conv_evalConv___closed__1;
    v___x_8547_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1;
    v___x_8548_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalConv___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_8549_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8545_,
        v___x_8546_,
        v___x_8547_,
        v___x_8548_,
    );
    return v___x_8549_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___boxed(
    mut v_a_8550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8551_: *mut LeanObject = core::ptr::null_mut();
    v_res_8551_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
    return v_res_8551_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3()
-> *mut LeanObject {
    let mut v___x_8578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8580_: *mut LeanObject = core::ptr::null_mut();
    v___x_8578_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1;
    v___x_8579_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6;
    v___x_8580_ = l_Lean_addBuiltinDeclarationRanges(v___x_8578_, v___x_8579_);
    return v___x_8580_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___boxed(
    mut v_a_8581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8582_: *mut LeanObject = core::ptr::null_mut();
    v_res_8582_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
    return v_res_8582_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalFirst(
    mut v_a_8583_: *mut LeanObject,
    mut v_a_8584_: *mut LeanObject,
    mut v_a_8585_: *mut LeanObject,
    mut v_a_8586_: *mut LeanObject,
    mut v_a_8587_: *mut LeanObject,
    mut v_a_8588_: *mut LeanObject,
    mut v_a_8589_: *mut LeanObject,
    mut v_a_8590_: *mut LeanObject,
    mut v_a_8591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8593_: *mut LeanObject = core::ptr::null_mut();
    v___x_8593_ = l_Lean_Elab_Tactic_evalFirst(
        v_a_8583_, v_a_8584_, v_a_8585_, v_a_8586_, v_a_8587_, v_a_8588_, v_a_8589_, v_a_8590_,
        v_a_8591_,
    );
    return v___x_8593_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalFirst___boxed(
    mut v_a_8594_: *mut LeanObject,
    mut v_a_8595_: *mut LeanObject,
    mut v_a_8596_: *mut LeanObject,
    mut v_a_8597_: *mut LeanObject,
    mut v_a_8598_: *mut LeanObject,
    mut v_a_8599_: *mut LeanObject,
    mut v_a_8600_: *mut LeanObject,
    mut v_a_8601_: *mut LeanObject,
    mut v_a_8602_: *mut LeanObject,
    mut v_a_8603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8604_: *mut LeanObject = core::ptr::null_mut();
    v_res_8604_ = l_Lean_Elab_Tactic_Conv_evalFirst(
        v_a_8594_, v_a_8595_, v_a_8596_, v_a_8597_, v_a_8598_, v_a_8599_, v_a_8600_, v_a_8601_,
        v_a_8602_,
    );
    lean_dec(v_a_8602_);
    lean_dec_ref(v_a_8601_);
    lean_dec(v_a_8600_);
    lean_dec_ref(v_a_8599_);
    lean_dec(v_a_8598_);
    lean_dec_ref(v_a_8597_);
    lean_dec(v_a_8596_);
    lean_dec_ref(v_a_8595_);
    lean_dec(v_a_8594_);
    return v_res_8604_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1()
-> *mut LeanObject {
    let mut v___f_8621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8625_: *mut LeanObject = core::ptr::null_mut();
    v___f_8621_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0;
    v___x_8622_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_8623_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2;
    v___x_8624_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4;
    v___x_8625_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8622_,
        v___x_8623_,
        v___x_8624_,
        v___f_8621_,
    );
    return v___x_8625_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___boxed(
    mut v_a_8626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8627_: *mut LeanObject = core::ptr::null_mut();
    v_res_8627_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
    return v_res_8627_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3()
-> *mut LeanObject {
    let mut v___x_8654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8656_: *mut LeanObject = core::ptr::null_mut();
    v___x_8654_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4;
    v___x_8655_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6;
    v___x_8656_ = l_Lean_addBuiltinDeclarationRanges(v___x_8654_, v___x_8655_);
    return v___x_8656_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___boxed(
    mut v_a_8657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8658_: *mut LeanObject = core::ptr::null_mut();
    v_res_8658_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
    return v_res_8658_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BuiltinTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_BuiltinTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
}

// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Specialize
// Imports: Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Do.ProofMode.MGoal Lean.Elab.Tactic.Do.ProofMode.Basic Lean.Elab.Tactic.Do.ProofMode.Focus
use crate::r#gen::Init::Control::Option::l_OptionT_instInhabitedOfPure___redArg;
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Name_mkStr5, l_Lean_Name_mkStr6, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId, l_Lean_Syntax_isIdent,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_pure___boxed,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Exception_isRuntime,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed,
    l_Lean_Elab_Tactic_pushGoals___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
    l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Focus::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Focus, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp,
    l_Lean_Elab_Tactic_Do_ProofMode_focusHyp,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal, l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21,
    l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo, l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, l_Lean_Elab_Tactic_elabTerm,
    l_Lean_Elab_Tactic_elabTermWithHoles, runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed,
    l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_beta, l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkApp3, l_Lean_mkApp5,
    l_Lean_mkApp6, l_Lean_mkApp7, l_Lean_mkApp8, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkSort,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::SynthInstance::{
    l_Lean_Meta_synthInstance, l_Lean_Meta_synthInstance_x3f,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
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
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt, lean_panic_fn_borrowed,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_9, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,15847151208953044930 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,7648019047378041818 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,9066735804595760508 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,5409699204079762053 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,14659826576719934041 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,4071431237389361899 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [83, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,9462462166819415419 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,8941658863464539270 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,18371068392043730063 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,2784220834938476977 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,9236383810522323512 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,17269713941526591656 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,2912219214903689382 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,254604373045785963 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,4954030756315748014 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,7235973974349327831 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,17684124286026840217 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,17544608138744826672 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,13147954315121438976 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,14217083148303276318 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,15007254394173596866 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,((( 1458348229 as usize) << 1) | 1) as *mut LeanObject,6766886947154232386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,16205549093318484973 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,6549976805098378925 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,9879058081985722496 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value:
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
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value:
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
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2_value:
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
    m_data: [105, 109, 112, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__3_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [105, 109, 112, 95, 115, 116, 97, 116, 101, 102, 117, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_0:
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
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_2:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,4902770359947064127 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value_aux_4
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__3_value
        ) as *mut LeanObject,
        1811097548778139097 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122,
        101, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [32, 119, 105, 116, 104, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__9_value:
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10_value:
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
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__9_value
        ) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 97, 116, 101, 102, 117, 108, 108, 121, 32, 115, 112, 101, 99, 105, 97, 108, 105,
        122, 101, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [46, 32, 78, 101, 119, 32, 71, 111, 97, 108, 58, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,17651876509044871153 as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [73, 115, 80, 117, 114, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_2: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__3_value
            ) as *mut LeanObject,
            18273640022974733293 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5_value: LeanStringObject<
    21,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        80, 114, 111, 112, 65, 115, 83, 80, 114, 101, 100, 84, 97, 117, 116, 111, 108, 111, 103,
        121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_2: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5_value
            ) as *mut LeanObject,
            2932917581903347504 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7_value: LeanStringObject<
    9,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 109, 112, 95, 112, 117, 114, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_2: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,4902770359947064127 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value_aux_4
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__7_value
            ) as *mut LeanObject,
            18101951619398857154 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9_value: LeanStringObject<
    19,
> = LeanStringObject {
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
        80, 117, 114, 101, 108, 121, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [112, 117, 114, 101, 95, 116, 97, 117, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_2: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,4902770359947064127 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value_aux_4
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__11_value)
            as *mut LeanObject,
        7656503729508035226 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13_value: LeanStringObject<
    13,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [116, 97, 117, 116, 111, 108, 111, 103, 105, 99, 97, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_2: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__13_value)
            as *mut LeanObject,
        14581852829424383138 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15_value: LeanStringObject<
    41,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80,
        114, 111, 111, 102, 77, 111, 100, 101, 46, 83, 112, 101, 99, 105, 97, 108, 105, 122, 101,
        0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16_value: LeanStringObject<
    49,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80,
        114, 111, 111, 102, 77, 111, 100, 101, 46, 109, 83, 112, 101, 99, 105, 97, 108, 105, 122,
        101, 73, 109, 112, 80, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17_value: LeanStringObject<
    43,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        80, 114, 101, 99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 111, 102, 32, 115, 112, 101,
        99, 105, 97, 108, 105, 122, 101, 73, 109, 112, 80, 117, 114, 101, 32, 118, 105, 111, 108,
        97, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [102, 111, 114, 97, 108, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_2: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,4902770359947064127 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value_aux_4
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0_value)
                as *mut LeanObject,
            10596647548066653247 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2_value: LeanStringObject<
    13,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [73, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4_value: LeanStringObject<
    48,
> = LeanStringObject {
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80,
        114, 111, 111, 102, 77, 111, 100, 101, 46, 109, 83, 112, 101, 99, 105, 97, 108, 105, 122,
        101, 70, 111, 114, 97, 108, 108, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5_value: LeanStringObject<
    42,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        80, 114, 101, 99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 111, 102, 32, 115, 112, 101,
        99, 105, 97, 108, 105, 122, 101, 70, 111, 114, 97, 108, 108, 32, 118, 105, 111, 108, 97,
        116, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0_value
) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 110, 116, 97, 105, 108, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 110, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0_value:
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
    m_data: [102, 111, 99, 117, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80,
        114, 111, 111, 102, 77, 111, 100, 101, 46, 101, 108, 97, 98, 77, 83, 112, 101, 99, 105, 97,
        108, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2_value:
    LeanStringObject<33> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        73, 110, 118, 97, 114, 105, 97, 110, 116, 32, 111, 102, 32, 115, 112, 101, 99, 105, 97,
        108, 105, 122, 101, 32, 118, 105, 111, 108, 97, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4_value:
    LeanStringObject<21> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114,
        32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6_value:
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
    m_data: [96, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__1_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [109, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__1_value)
                as *mut LeanObject,
            15094741897836356535 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 108, 97, 98, 77, 83, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__0_value) as *mut LeanObject,4084590471603909684 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value_aux_0:
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
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1_value:
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
    m_data: [112, 117, 114, 101, 95, 115, 116, 97, 114, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2_value:
    LeanStringObject<50> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80,
        114, 111, 111, 102, 77, 111, 100, 101, 46, 101, 108, 97, 98, 77, 115, 112, 101, 99, 105,
        97, 108, 105, 122, 101, 80, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3_value:
    LeanStringObject<38> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        73, 110, 118, 97, 114, 105, 97, 110, 116, 32, 111, 102, 32, 115, 112, 101, 99, 105, 97,
        108, 105, 122, 101, 95, 112, 117, 114, 101, 32, 118, 105, 111, 108, 97, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__0_value: LeanStringObject<
    16,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        109, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 80, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_1: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__0_value)
            as *mut LeanObject,
        9159418223907454752 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 112, 112, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_1: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_2: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__2_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value: LeanCtorObject<
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
            l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__3_value)
            as *mut LeanObject,
        12966880221525079621 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 108, 97, 98, 77, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 80, 117, 114, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2__value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__0_value) as *mut LeanObject,15700459910593837462 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: u8 = 0;
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    v___x_2345_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
    v___x_2346_ = 0;
    v___x_2347_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
    v___x_2348_ = l_Lean_registerTraceClass(v___x_2345_, v___x_2346_, v___x_2347_);
    return v___x_2348_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2____boxed(
    mut v_a_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2350_: *mut LeanObject = core::ptr::null_mut();
    v_res_2350_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_();
    return v_res_2350_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(
    mut v_msgData_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
    mut v___y_2353_: *mut LeanObject,
    mut v___y_2354_: *mut LeanObject,
    mut v___y_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    v___x_2357_ = lean_st_ref_get(v___y_2355_);
    v_env_2358_ = lean_ctor_get(v___x_2357_, 0);
    lean_inc_ref(v_env_2358_);
    lean_dec(v___x_2357_);
    v___x_2359_ = lean_st_ref_get(v___y_2353_);
    v_mctx_2360_ = lean_ctor_get(v___x_2359_, 0);
    lean_inc_ref(v_mctx_2360_);
    lean_dec(v___x_2359_);
    v_lctx_2361_ = lean_ctor_get(v___y_2352_, 2);
    v_options_2362_ = lean_ctor_get(v___y_2354_, 2);
    lean_inc_ref(v_options_2362_);
    lean_inc_ref(v_lctx_2361_);
    v___x_2363_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2363_, 0, v_env_2358_);
    lean_ctor_set(v___x_2363_, 1, v_mctx_2360_);
    lean_ctor_set(v___x_2363_, 2, v_lctx_2361_);
    lean_ctor_set(v___x_2363_, 3, v_options_2362_);
    v___x_2364_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2364_, 0, v___x_2363_);
    lean_ctor_set(v___x_2364_, 1, v_msgData_2351_);
    v___x_2365_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2365_, 0, v___x_2364_);
    return v___x_2365_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0___boxed(
    mut v_msgData_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
    mut v___y_2369_: *mut LeanObject,
    mut v___y_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2372_: *mut LeanObject = core::ptr::null_mut();
    v_res_2372_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msgData_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
    lean_dec(v___y_2370_);
    lean_dec_ref(v___y_2369_);
    lean_dec(v___y_2368_);
    lean_dec_ref(v___y_2367_);
    return v_res_2372_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: f64 = 0.0;
    v___x_2373_ = lean_unsigned_to_nat(0);
    v___x_2374_ = lean_float_of_nat(v___x_2373_);
    return v___x_2374_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(
    mut v_cls_2378_: *mut LeanObject,
    mut v_msg_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v_tid_2404_: u64 = 0;
    let mut v_traces_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: f64 = 0.0;
    let mut v___x_2411_: u8 = 0;
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut v_isSharedCheck_2430_: u8 = 0;
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2385_ = lean_ctor_get(v___y_2382_, 5);
                v___x_2386_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
                v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
                v_isSharedCheck_2431_ = (!lean_is_exclusive(v___x_2386_)) as u8;
                if v_isSharedCheck_2431_ == 0 {
                    v___x_2389_ = v___x_2386_;
                    v_isShared_2390_ = v_isSharedCheck_2431_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2387_);
                    lean_dec(v___x_2386_);
                    v___x_2389_ = lean_box(0);
                    v_isShared_2390_ = v_isSharedCheck_2431_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2391_ = lean_st_ref_take(v___y_2383_);
                v_traceState_2392_ = lean_ctor_get(v___x_2391_, 4);
                v_env_2393_ = lean_ctor_get(v___x_2391_, 0);
                v_nextMacroScope_2394_ = lean_ctor_get(v___x_2391_, 1);
                v_ngen_2395_ = lean_ctor_get(v___x_2391_, 2);
                v_auxDeclNGen_2396_ = lean_ctor_get(v___x_2391_, 3);
                v_cache_2397_ = lean_ctor_get(v___x_2391_, 5);
                v_messages_2398_ = lean_ctor_get(v___x_2391_, 6);
                v_infoState_2399_ = lean_ctor_get(v___x_2391_, 7);
                v_snapshotTasks_2400_ = lean_ctor_get(v___x_2391_, 8);
                v_isSharedCheck_2430_ = (!lean_is_exclusive(v___x_2391_)) as u8;
                if v_isSharedCheck_2430_ == 0 {
                    v___x_2402_ = v___x_2391_;
                    v_isShared_2403_ = v_isSharedCheck_2430_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2400_);
                    lean_inc(v_infoState_2399_);
                    lean_inc(v_messages_2398_);
                    lean_inc(v_cache_2397_);
                    lean_inc(v_traceState_2392_);
                    lean_inc(v_auxDeclNGen_2396_);
                    lean_inc(v_ngen_2395_);
                    lean_inc(v_nextMacroScope_2394_);
                    lean_inc(v_env_2393_);
                    lean_dec(v___x_2391_);
                    v___x_2402_ = lean_box(0);
                    v_isShared_2403_ = v_isSharedCheck_2430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2404_ = lean_ctor_get_uint64(
                    v_traceState_2392_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2405_ = lean_ctor_get(v_traceState_2392_, 0);
                v_isSharedCheck_2429_ = (!lean_is_exclusive(v_traceState_2392_)) as u8;
                if v_isSharedCheck_2429_ == 0 {
                    v___x_2407_ = v_traceState_2392_;
                    v_isShared_2408_ = v_isSharedCheck_2429_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2405_);
                    lean_dec(v_traceState_2392_);
                    v___x_2407_ = lean_box(0);
                    v_isShared_2408_ = v_isSharedCheck_2429_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2409_ = lean_box(0);
                v___x_2410_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__0);
                v___x_2411_ = 0;
                v___x_2412_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__1;
                v___x_2413_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2413_, 0, v_cls_2378_);
                lean_ctor_set(v___x_2413_, 1, v___x_2409_);
                lean_ctor_set(v___x_2413_, 2, v___x_2412_);
                lean_ctor_set_float(
                    v___x_2413_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2410_,
                );
                lean_ctor_set_float(
                    v___x_2413_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2410_,
                );
                lean_ctor_set_uint8(
                    v___x_2413_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2411_,
                );
                v___x_2414_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___closed__2;
                v___x_2415_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2415_, 0, v___x_2413_);
                lean_ctor_set(v___x_2415_, 1, v_a_2387_);
                lean_ctor_set(v___x_2415_, 2, v___x_2414_);
                lean_inc(v_ref_2385_);
                v___x_2416_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2416_, 0, v_ref_2385_);
                lean_ctor_set(v___x_2416_, 1, v___x_2415_);
                v___x_2417_ = l_Lean_PersistentArray_push___redArg(v_traces_2405_, v___x_2416_);
                if v_isShared_2408_ == 0 {
                    lean_ctor_set(v___x_2407_, 0, v___x_2417_);
                    v___x_2419_ = v___x_2407_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2417_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2428_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2404_,
                    );
                    v___x_2419_ = v_reuseFailAlloc_2428_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2403_ == 0 {
                    lean_ctor_set(v___x_2402_, 4, v___x_2419_);
                    v___x_2421_ = v___x_2402_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_env_2393_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_nextMacroScope_2394_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_ngen_2395_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 3, v_auxDeclNGen_2396_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 4, v___x_2419_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 5, v_cache_2397_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 6, v_messages_2398_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 7, v_infoState_2399_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 8, v_snapshotTasks_2400_);
                    v___x_2421_ = v_reuseFailAlloc_2427_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2422_ = lean_st_ref_set(v___y_2383_, v___x_2421_);
                v___x_2423_ = lean_box(0);
                if v_isShared_2390_ == 0 {
                    lean_ctor_set(v___x_2389_, 0, v___x_2423_);
                    v___x_2425_ = v___x_2389_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
                    v___x_2425_ = v_reuseFailAlloc_2426_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg___boxed(
    mut v_cls_2432_: *mut LeanObject,
    mut v_msg_2433_: *mut LeanObject,
    mut v___y_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
    mut v___y_2436_: *mut LeanObject,
    mut v___y_2437_: *mut LeanObject,
    mut v___y_2438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2439_: *mut LeanObject = core::ptr::null_mut();
    v_res_2439_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_2432_, v_msg_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
    lean_dec(v___y_2437_);
    lean_dec_ref(v___y_2436_);
    lean_dec(v___y_2435_);
    lean_dec_ref(v___y_2434_);
    return v_res_2439_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(
    mut v_msg_2440_: *mut LeanObject,
    mut v___y_2441_: *mut LeanObject,
    mut v___y_2442_: *mut LeanObject,
    mut v___y_2443_: *mut LeanObject,
    mut v___y_2444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2451_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2446_ = lean_ctor_get(v___y_2443_, 5);
                v___x_2447_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0_spec__0(v_msg_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
                v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
                v_isSharedCheck_2456_ = (!lean_is_exclusive(v___x_2447_)) as u8;
                if v_isSharedCheck_2456_ == 0 {
                    v___x_2450_ = v___x_2447_;
                    v_isShared_2451_ = v_isSharedCheck_2456_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2448_);
                    lean_dec(v___x_2447_);
                    v___x_2450_ = lean_box(0);
                    v_isShared_2451_ = v_isSharedCheck_2456_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2446_);
                v___x_2452_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2452_, 0, v_ref_2446_);
                lean_ctor_set(v___x_2452_, 1, v_a_2448_);
                if v_isShared_2451_ == 0 {
                    lean_ctor_set_tag(v___x_2450_, 1);
                    lean_ctor_set(v___x_2450_, 0, v___x_2452_);
                    v___x_2454_ = v___x_2450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2452_);
                    v___x_2454_ = v_reuseFailAlloc_2455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg___boxed(
    mut v_msg_2457_: *mut LeanObject,
    mut v___y_2458_: *mut LeanObject,
    mut v___y_2459_: *mut LeanObject,
    mut v___y_2460_: *mut LeanObject,
    mut v___y_2461_: *mut LeanObject,
    mut v___y_2462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2463_: *mut LeanObject = core::ptr::null_mut();
    v_res_2463_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
    lean_dec(v___y_2461_);
    lean_dec_ref(v___y_2460_);
    lean_dec(v___y_2459_);
    lean_dec_ref(v___y_2458_);
    return v_res_2463_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6()
-> *mut LeanObject {
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__5;
    v___x_2477_ = l_Lean_stringToMessageData(v___x_2476_);
    return v___x_2477_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8()
-> *mut LeanObject {
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    v___x_2479_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__7;
    v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
    return v___x_2480_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11()
-> *mut LeanObject {
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    v___x_2484_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
    v___x_2485_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__10;
    v___x_2486_ = l_Lean_Name_append(v___x_2485_, v___x_2484_);
    return v___x_2486_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13()
-> *mut LeanObject {
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    v___x_2488_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__12;
    v___x_2489_ = l_Lean_stringToMessageData(v___x_2488_);
    return v___x_2489_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15()
-> *mut LeanObject {
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    v___x_2491_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__14;
    v___x_2492_ = l_Lean_stringToMessageData(v___x_2491_);
    return v___x_2492_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(
    mut v_P_2493_: *mut LeanObject,
    mut v_QR_2494_: *mut LeanObject,
    mut v_arg_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
    mut v_a_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
    mut v_a_2501_: *mut LeanObject,
    mut v_a_2502_: *mut LeanObject,
    mut v_a_2503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: u8 = 0;
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v_p_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uniq_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2529_: u8 = 0;
    let mut v_arg_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v_tail_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2554_: u8 = 0;
    let mut v_focusHyp_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restHyps_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2563_: u8 = 0;
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v_options_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2570_: u8 = 0;
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2609_: u8 = 0;
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2613_: u8 = 0;
    let mut v_a_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2621_: u8 = 0;
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: u8 = 0;
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2641_: u8 = 0;
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut v_isSharedCheck_2646_: u8 = 0;
    let mut v_unused_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2651_: u8 = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2661_: u8 = 0;
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2666_: u8 = 0;
    let mut v_unused_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2668_: u8 = 0;
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2508_ = l_Lean_Syntax_isIdent(v_arg_2495_);
                if v___x_2508_ == 0 {
                    lean_dec(v_arg_2495_);
                    lean_dec_ref(v_QR_2494_);
                    lean_dec_ref(v_P_2493_);
                    v___x_2509_ = lean_box(0);
                    v___x_2510_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2510_, 0, v___x_2509_);
                    return v___x_2510_;
                } else {
                    lean_inc_ref(v_QR_2494_);
                    v___x_2511_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_2494_);
                    if lean_obj_tag(v___x_2511_) == 1 {
                        v_val_2512_ = lean_ctor_get(v___x_2511_, 0);
                        v_isSharedCheck_2668_ = (!lean_is_exclusive(v___x_2511_)) as u8;
                        if v_isSharedCheck_2668_ == 0 {
                            v___x_2514_ = v___x_2511_;
                            v_isShared_2515_ = v_isSharedCheck_2668_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_2512_);
                            lean_dec(v___x_2511_);
                            v___x_2514_ = lean_box(0);
                            v_isShared_2515_ = v_isSharedCheck_2668_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2511_);
                        lean_dec(v_arg_2495_);
                        lean_dec_ref(v_QR_2494_);
                        lean_dec_ref(v_P_2493_);
                        v___x_2669_ = lean_box(0);
                        v___x_2670_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2670_, 0, v___x_2669_);
                        return v___x_2670_;
                    }
                }
            }
            1 => {
                v___x_2506_ = lean_box(0);
                v___x_2507_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2507_, 0, v___x_2506_);
                return v___x_2507_;
            }
            2 => {
                v_p_2516_ = lean_ctor_get(v_val_2512_, 2);
                lean_inc_ref(v_p_2516_);
                if lean_obj_tag(v_p_2516_) == 5 {
                    v_fn_2517_ = lean_ctor_get(v_p_2516_, 0);
                    if lean_obj_tag(v_fn_2517_) == 5 {
                        v_fn_2518_ = lean_ctor_get(v_fn_2517_, 0);
                        if lean_obj_tag(v_fn_2518_) == 5 {
                            v_fn_2519_ = lean_ctor_get(v_fn_2518_, 0);
                            if lean_obj_tag(v_fn_2519_) == 4 {
                                v_declName_2520_ = lean_ctor_get(v_fn_2519_, 0);
                                if lean_obj_tag(v_declName_2520_) == 1 {
                                    v_pre_2521_ = lean_ctor_get(v_declName_2520_, 0);
                                    if lean_obj_tag(v_pre_2521_) == 1 {
                                        v_pre_2522_ = lean_ctor_get(v_pre_2521_, 0);
                                        if lean_obj_tag(v_pre_2522_) == 1 {
                                            v_pre_2523_ = lean_ctor_get(v_pre_2522_, 0);
                                            if lean_obj_tag(v_pre_2523_) == 1 {
                                                v_pre_2524_ = lean_ctor_get(v_pre_2523_, 0);
                                                if lean_obj_tag(v_pre_2524_) == 0 {
                                                    v_name_2525_ = lean_ctor_get(v_val_2512_, 0);
                                                    v_uniq_2526_ = lean_ctor_get(v_val_2512_, 1);
                                                    v_isSharedCheck_2666_ =
                                                        (!lean_is_exclusive(v_val_2512_)) as u8;
                                                    if v_isSharedCheck_2666_ == 0 {
                                                        v_unused_2667_ =
                                                            lean_ctor_get(v_val_2512_, 2);
                                                        lean_dec(v_unused_2667_);
                                                        v___x_2528_ = v_val_2512_;
                                                        v_isShared_2529_ = v_isSharedCheck_2666_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_uniq_2526_);
                                                        lean_inc(v_name_2525_);
                                                        lean_dec(v_val_2512_);
                                                        v___x_2528_ = lean_box(0);
                                                        v_isShared_2529_ = v_isSharedCheck_2666_;
                                                        state = 3;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref_known(v_p_2516_, 2);
                                                    lean_del_object(v___x_2514_);
                                                    lean_dec(v_val_2512_);
                                                    lean_dec(v_arg_2495_);
                                                    lean_dec_ref(v_QR_2494_);
                                                    lean_dec_ref(v_P_2493_);
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref_known(v_p_2516_, 2);
                                                lean_del_object(v___x_2514_);
                                                lean_dec(v_val_2512_);
                                                lean_dec(v_arg_2495_);
                                                lean_dec_ref(v_QR_2494_);
                                                lean_dec_ref(v_P_2493_);
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref_known(v_p_2516_, 2);
                                            lean_del_object(v___x_2514_);
                                            lean_dec(v_val_2512_);
                                            lean_dec(v_arg_2495_);
                                            lean_dec_ref(v_QR_2494_);
                                            lean_dec_ref(v_P_2493_);
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref_known(v_p_2516_, 2);
                                        lean_del_object(v___x_2514_);
                                        lean_dec(v_val_2512_);
                                        lean_dec(v_arg_2495_);
                                        lean_dec_ref(v_QR_2494_);
                                        lean_dec_ref(v_P_2493_);
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_p_2516_, 2);
                                    lean_del_object(v___x_2514_);
                                    lean_dec(v_val_2512_);
                                    lean_dec(v_arg_2495_);
                                    lean_dec_ref(v_QR_2494_);
                                    lean_dec_ref(v_P_2493_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_p_2516_, 2);
                                lean_del_object(v___x_2514_);
                                lean_dec(v_val_2512_);
                                lean_dec(v_arg_2495_);
                                lean_dec_ref(v_QR_2494_);
                                lean_dec_ref(v_P_2493_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_p_2516_, 2);
                            lean_del_object(v___x_2514_);
                            lean_dec(v_val_2512_);
                            lean_dec(v_arg_2495_);
                            lean_dec_ref(v_QR_2494_);
                            lean_dec_ref(v_P_2493_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_p_2516_, 2);
                        lean_del_object(v___x_2514_);
                        lean_dec(v_val_2512_);
                        lean_dec(v_arg_2495_);
                        lean_dec_ref(v_QR_2494_);
                        lean_dec_ref(v_P_2493_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_2516_);
                    lean_del_object(v___x_2514_);
                    lean_dec(v_val_2512_);
                    lean_dec(v_arg_2495_);
                    lean_dec_ref(v_QR_2494_);
                    lean_dec_ref(v_P_2493_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_arg_2530_ = lean_ctor_get(v_p_2516_, 1);
                v_arg_2531_ = lean_ctor_get(v_fn_2517_, 1);
                v_arg_2532_ = lean_ctor_get(v_fn_2518_, 1);
                v_us_2533_ = lean_ctor_get(v_fn_2519_, 1);
                v_str_2534_ = lean_ctor_get(v_declName_2520_, 1);
                v_str_2535_ = lean_ctor_get(v_pre_2521_, 1);
                v_str_2536_ = lean_ctor_get(v_pre_2522_, 1);
                v_str_2537_ = lean_ctor_get(v_pre_2523_, 1);
                v___x_2538_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0;
                v___x_2539_ = lean_string_dec_eq(v_str_2537_, v___x_2538_);
                if v___x_2539_ == 0 {
                    lean_del_object(v___x_2528_);
                    lean_dec(v_uniq_2526_);
                    lean_dec(v_name_2525_);
                    lean_dec_ref_known(v_p_2516_, 2);
                    lean_del_object(v___x_2514_);
                    lean_dec(v_arg_2495_);
                    lean_dec_ref(v_QR_2494_);
                    lean_dec_ref(v_P_2493_);
                    state = 1;
                    continue;
                } else {
                    v___x_2540_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                    v___x_2541_ = lean_string_dec_eq(v_str_2536_, v___x_2540_);
                    if v___x_2541_ == 0 {
                        lean_del_object(v___x_2528_);
                        lean_dec(v_uniq_2526_);
                        lean_dec(v_name_2525_);
                        lean_dec_ref_known(v_p_2516_, 2);
                        lean_del_object(v___x_2514_);
                        lean_dec(v_arg_2495_);
                        lean_dec_ref(v_QR_2494_);
                        lean_dec_ref(v_P_2493_);
                        state = 1;
                        continue;
                    } else {
                        v___x_2542_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1;
                        v___x_2543_ = lean_string_dec_eq(v_str_2535_, v___x_2542_);
                        if v___x_2543_ == 0 {
                            lean_del_object(v___x_2528_);
                            lean_dec(v_uniq_2526_);
                            lean_dec(v_name_2525_);
                            lean_dec_ref_known(v_p_2516_, 2);
                            lean_del_object(v___x_2514_);
                            lean_dec(v_arg_2495_);
                            lean_dec_ref(v_QR_2494_);
                            lean_dec_ref(v_P_2493_);
                            state = 1;
                            continue;
                        } else {
                            v___x_2544_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2;
                            v___x_2545_ = lean_string_dec_eq(v_str_2534_, v___x_2544_);
                            if v___x_2545_ == 0 {
                                lean_del_object(v___x_2528_);
                                lean_dec(v_uniq_2526_);
                                lean_dec(v_name_2525_);
                                lean_dec_ref_known(v_p_2516_, 2);
                                lean_del_object(v___x_2514_);
                                lean_dec(v_arg_2495_);
                                lean_dec_ref(v_QR_2494_);
                                lean_dec_ref(v_P_2493_);
                                state = 1;
                                continue;
                            } else {
                                if lean_obj_tag(v_us_2533_) == 1 {
                                    v_tail_2546_ = lean_ctor_get(v_us_2533_, 1);
                                    if lean_obj_tag(v_tail_2546_) == 0 {
                                        v_head_2547_ = lean_ctor_get(v_us_2533_, 0);
                                        lean_inc_ref(v_P_2493_);
                                        lean_inc_ref_n(v_arg_2532_, 2);
                                        lean_inc_n(v_head_2547_, 2);
                                        v___x_2548_ =
                                            l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                                                v_head_2547_,
                                                v_arg_2532_,
                                                v_P_2493_,
                                                v_QR_2494_,
                                            );
                                        v___x_2549_ = l_Lean_Syntax_getId(v_arg_2495_);
                                        v___x_2550_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(
                                            v_head_2547_,
                                            v_arg_2532_,
                                            v___x_2548_,
                                            v___x_2549_,
                                        );
                                        lean_dec(v___x_2549_);
                                        if lean_obj_tag(v___x_2550_) == 1 {
                                            lean_del_object(v___x_2514_);
                                            v_val_2551_ = lean_ctor_get(v___x_2550_, 0);
                                            v_isSharedCheck_2661_ =
                                                (!lean_is_exclusive(v___x_2550_)) as u8;
                                            if v_isSharedCheck_2661_ == 0 {
                                                v___x_2553_ = v___x_2550_;
                                                v_isShared_2554_ = v_isSharedCheck_2661_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_inc(v_val_2551_);
                                                lean_dec(v___x_2550_);
                                                v___x_2553_ = lean_box(0);
                                                v_isShared_2554_ = v_isSharedCheck_2661_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v___x_2550_);
                                            lean_del_object(v___x_2528_);
                                            lean_dec(v_uniq_2526_);
                                            lean_dec(v_name_2525_);
                                            lean_dec_ref_known(v_p_2516_, 2);
                                            lean_dec(v_arg_2495_);
                                            lean_dec_ref(v_P_2493_);
                                            v___x_2662_ = lean_box(0);
                                            if v_isShared_2515_ == 0 {
                                                lean_ctor_set_tag(v___x_2514_, 0);
                                                lean_ctor_set(v___x_2514_, 0, v___x_2662_);
                                                v___x_2664_ = v___x_2514_;
                                                state = 21;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_2665_ =
                                                    lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(
                                                    v_reuseFailAlloc_2665_,
                                                    0,
                                                    v___x_2662_,
                                                );
                                                v___x_2664_ = v_reuseFailAlloc_2665_;
                                                state = 21;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_del_object(v___x_2528_);
                                        lean_dec(v_uniq_2526_);
                                        lean_dec(v_name_2525_);
                                        lean_dec_ref_known(v_p_2516_, 2);
                                        lean_del_object(v___x_2514_);
                                        lean_dec(v_arg_2495_);
                                        lean_dec_ref(v_QR_2494_);
                                        lean_dec_ref(v_P_2493_);
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_2528_);
                                    lean_dec(v_uniq_2526_);
                                    lean_dec(v_name_2525_);
                                    lean_dec_ref_known(v_p_2516_, 2);
                                    lean_del_object(v___x_2514_);
                                    lean_dec(v_arg_2495_);
                                    lean_dec_ref(v_QR_2494_);
                                    lean_dec_ref(v_P_2493_);
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            4 => {
                v_focusHyp_2555_ = lean_ctor_get(v_val_2551_, 0);
                lean_inc_ref_n(v_focusHyp_2555_, 2);
                v_restHyps_2556_ = lean_ctor_get(v_val_2551_, 1);
                lean_inc_ref(v_restHyps_2556_);
                v_proof_2557_ = lean_ctor_get(v_val_2551_, 2);
                lean_inc_ref(v_proof_2557_);
                lean_dec(v_val_2551_);
                v___x_2558_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_2555_);
                if lean_obj_tag(v___x_2558_) == 1 {
                    lean_del_object(v___x_2553_);
                    v_val_2559_ = lean_ctor_get(v___x_2558_, 0);
                    v_isSharedCheck_2656_ = (!lean_is_exclusive(v___x_2558_)) as u8;
                    if v_isSharedCheck_2656_ == 0 {
                        v___x_2561_ = v___x_2558_;
                        v_isShared_2562_ = v_isSharedCheck_2656_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_2559_);
                        lean_dec(v___x_2558_);
                        v___x_2561_ = lean_box(0);
                        v_isShared_2562_ = v_isSharedCheck_2656_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2558_);
                    lean_dec_ref(v_proof_2557_);
                    lean_dec_ref(v_restHyps_2556_);
                    lean_dec_ref(v_focusHyp_2555_);
                    lean_del_object(v___x_2528_);
                    lean_dec(v_uniq_2526_);
                    lean_dec(v_name_2525_);
                    lean_dec_ref_known(v_p_2516_, 2);
                    lean_dec(v_arg_2495_);
                    lean_dec_ref(v_P_2493_);
                    v___x_2657_ = lean_box(0);
                    if v_isShared_2554_ == 0 {
                        lean_ctor_set_tag(v___x_2553_, 0);
                        lean_ctor_set(v___x_2553_, 0, v___x_2657_);
                        v___x_2659_ = v___x_2553_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
                        v___x_2659_ = v_reuseFailAlloc_2660_;
                        state = 20;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2563_ = 0;
                lean_inc_ref(v_arg_2532_);
                v___x_2564_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                    v_arg_2495_,
                    v_arg_2532_,
                    v_val_2559_,
                    v___x_2563_,
                    v_a_2500_,
                    v_a_2501_,
                    v_a_2502_,
                    v_a_2503_,
                );
                if lean_obj_tag(v___x_2564_) == 0 {
                    v_isSharedCheck_2646_ = (!lean_is_exclusive(v___x_2564_)) as u8;
                    if v_isSharedCheck_2646_ == 0 {
                        v_unused_2647_ = lean_ctor_get(v___x_2564_, 0);
                        lean_dec(v_unused_2647_);
                        v___x_2566_ = v___x_2564_;
                        v_isShared_2567_ = v_isSharedCheck_2646_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v___x_2564_);
                        v___x_2566_ = lean_box(0);
                        v_isShared_2567_ = v_isSharedCheck_2646_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2561_);
                    lean_dec_ref(v_proof_2557_);
                    lean_dec_ref(v_restHyps_2556_);
                    lean_dec_ref(v_focusHyp_2555_);
                    lean_del_object(v___x_2528_);
                    lean_dec(v_uniq_2526_);
                    lean_dec(v_name_2525_);
                    lean_dec_ref_known(v_p_2516_, 2);
                    lean_dec_ref(v_P_2493_);
                    v_a_2648_ = lean_ctor_get(v___x_2564_, 0);
                    v_isSharedCheck_2655_ = (!lean_is_exclusive(v___x_2564_)) as u8;
                    if v_isSharedCheck_2655_ == 0 {
                        v___x_2650_ = v___x_2564_;
                        v_isShared_2651_ = v_isSharedCheck_2655_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_2648_);
                        lean_dec(v___x_2564_);
                        v___x_2650_ = lean_box(0);
                        v_isShared_2651_ = v_isSharedCheck_2655_;
                        state = 18;
                        continue;
                    }
                }
            }
            6 => {
                v_options_2568_ = lean_ctor_get(v_a_2502_, 2);
                v_inheritedTraceOptions_2569_ = lean_ctor_get(v_a_2502_, 13);
                v_hasTrace_2570_ = lean_ctor_get_uint8(
                    v_options_2568_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_2571_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__4;
                lean_inc_ref(v_us_2533_);
                v___x_2572_ = l_Lean_mkConst(v___x_2571_, v_us_2533_);
                lean_inc_ref(v_arg_2530_);
                lean_inc_ref(v_focusHyp_2555_);
                lean_inc_ref(v_P_2493_);
                lean_inc_ref(v_arg_2532_);
                v___x_2573_ = l_Lean_mkApp6(
                    v___x_2572_,
                    v_arg_2532_,
                    v_P_2493_,
                    v_restHyps_2556_,
                    v_focusHyp_2555_,
                    v_arg_2530_,
                    v_proof_2557_,
                );
                if v_hasTrace_2570_ == 0 {
                    lean_dec_ref(v_P_2493_);
                    v___y_2587_ = v_a_2496_;
                    v___y_2588_ = v_a_2497_;
                    v___y_2589_ = v_a_2498_;
                    v___y_2590_ = v_a_2499_;
                    v___y_2591_ = v_a_2500_;
                    v___y_2592_ = v_a_2501_;
                    v___y_2593_ = v_a_2502_;
                    v___y_2594_ = v_a_2503_;
                    state = 11;
                    continue;
                } else {
                    v___x_2622_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                    v___x_2623_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
                    v___x_2624_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2569_,
                        v_options_2568_,
                        v___x_2623_,
                    );
                    if v___x_2624_ == 0 {
                        lean_dec_ref(v_P_2493_);
                        v___y_2587_ = v_a_2496_;
                        v___y_2588_ = v_a_2497_;
                        v___y_2589_ = v_a_2498_;
                        v___y_2590_ = v_a_2499_;
                        v___y_2591_ = v_a_2500_;
                        v___y_2592_ = v_a_2501_;
                        v___y_2593_ = v_a_2502_;
                        v___y_2594_ = v_a_2503_;
                        state = 11;
                        continue;
                    } else {
                        v___x_2625_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__13);
                        lean_inc_ref(v_p_2516_);
                        v___x_2626_ = l_Lean_MessageData_ofExpr(v_p_2516_);
                        v___x_2627_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2627_, 0, v___x_2625_);
                        lean_ctor_set(v___x_2627_, 1, v___x_2626_);
                        v___x_2628_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
                        v___x_2629_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2629_, 0, v___x_2627_);
                        lean_ctor_set(v___x_2629_, 1, v___x_2628_);
                        lean_inc_ref(v_focusHyp_2555_);
                        v___x_2630_ = l_Lean_MessageData_ofExpr(v_focusHyp_2555_);
                        v___x_2631_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2631_, 0, v___x_2629_);
                        lean_ctor_set(v___x_2631_, 1, v___x_2630_);
                        v___x_2632_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15);
                        v___x_2633_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2633_, 0, v___x_2631_);
                        lean_ctor_set(v___x_2633_, 1, v___x_2632_);
                        lean_inc_ref(v_arg_2530_);
                        lean_inc_ref(v_arg_2532_);
                        lean_inc(v_head_2547_);
                        v___x_2634_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                            v_head_2547_,
                            v_arg_2532_,
                            v_P_2493_,
                            v_arg_2530_,
                        );
                        v___x_2635_ = l_Lean_MessageData_ofExpr(v___x_2634_);
                        v___x_2636_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2636_, 0, v___x_2633_);
                        lean_ctor_set(v___x_2636_, 1, v___x_2635_);
                        v___x_2637_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_2622_, v___x_2636_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
                        if lean_obj_tag(v___x_2637_) == 0 {
                            lean_dec_ref_known(v___x_2637_, 1);
                            v___y_2587_ = v_a_2496_;
                            v___y_2588_ = v_a_2497_;
                            v___y_2589_ = v_a_2498_;
                            v___y_2590_ = v_a_2499_;
                            v___y_2591_ = v_a_2500_;
                            v___y_2592_ = v_a_2501_;
                            v___y_2593_ = v_a_2502_;
                            v___y_2594_ = v_a_2503_;
                            state = 11;
                            continue;
                        } else {
                            lean_dec_ref(v___x_2573_);
                            lean_del_object(v___x_2566_);
                            lean_del_object(v___x_2561_);
                            lean_dec_ref(v_focusHyp_2555_);
                            lean_del_object(v___x_2528_);
                            lean_dec(v_uniq_2526_);
                            lean_dec(v_name_2525_);
                            lean_dec_ref_known(v_p_2516_, 2);
                            v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
                            v_isSharedCheck_2645_ = (!lean_is_exclusive(v___x_2637_)) as u8;
                            if v_isSharedCheck_2645_ == 0 {
                                v___x_2640_ = v___x_2637_;
                                v_isShared_2641_ = v_isSharedCheck_2645_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_2638_);
                                lean_dec(v___x_2637_);
                                v___x_2640_ = lean_box(0);
                                v_isShared_2641_ = v_isSharedCheck_2645_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            7 => {
                if v_isShared_2529_ == 0 {
                    lean_ctor_set(v___x_2528_, 2, v_arg_2530_);
                    v___x_2576_ = v___x_2528_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_name_2525_);
                    lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_uniq_2526_);
                    lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_arg_2530_);
                    v___x_2576_ = v_reuseFailAlloc_2585_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2577_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2576_);
                v___x_2578_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2578_, 0, v___x_2577_);
                lean_ctor_set(v___x_2578_, 1, v___x_2573_);
                if v_isShared_2562_ == 0 {
                    lean_ctor_set(v___x_2561_, 0, v___x_2578_);
                    v___x_2580_ = v___x_2561_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2578_);
                    v___x_2580_ = v_reuseFailAlloc_2584_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2567_ == 0 {
                    lean_ctor_set(v___x_2566_, 0, v___x_2580_);
                    v___x_2582_ = v___x_2566_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
                    v___x_2582_ = v_reuseFailAlloc_2583_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2582_;
            }
            11 => {
                lean_inc_ref(v_arg_2531_);
                lean_inc_ref(v_focusHyp_2555_);
                v___x_2595_ = l_Lean_Meta_isExprDefEq(
                    v_focusHyp_2555_,
                    v_arg_2531_,
                    v___y_2591_,
                    v___y_2592_,
                    v___y_2593_,
                    v___y_2594_,
                );
                if lean_obj_tag(v___x_2595_) == 0 {
                    v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
                    lean_inc(v_a_2596_);
                    lean_dec_ref_known(v___x_2595_, 1);
                    v___x_2597_ = (lean_unbox(v_a_2596_) as u8);
                    lean_dec(v_a_2596_);
                    if v___x_2597_ == 0 {
                        lean_dec_ref(v___x_2573_);
                        lean_del_object(v___x_2566_);
                        lean_del_object(v___x_2561_);
                        lean_del_object(v___x_2528_);
                        lean_dec(v_uniq_2526_);
                        lean_dec(v_name_2525_);
                        v___x_2598_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__6);
                        v___x_2599_ = l_Lean_MessageData_ofExpr(v_p_2516_);
                        v___x_2600_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2600_, 0, v___x_2598_);
                        lean_ctor_set(v___x_2600_, 1, v___x_2599_);
                        v___x_2601_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
                        v___x_2602_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2602_, 0, v___x_2600_);
                        lean_ctor_set(v___x_2602_, 1, v___x_2601_);
                        v___x_2603_ = l_Lean_MessageData_ofExpr(v_focusHyp_2555_);
                        v___x_2604_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2604_, 0, v___x_2602_);
                        lean_ctor_set(v___x_2604_, 1, v___x_2603_);
                        v___x_2605_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_2604_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
                        v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
                        v_isSharedCheck_2613_ = (!lean_is_exclusive(v___x_2605_)) as u8;
                        if v_isSharedCheck_2613_ == 0 {
                            v___x_2608_ = v___x_2605_;
                            v_isShared_2609_ = v_isSharedCheck_2613_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2606_);
                            lean_dec(v___x_2605_);
                            v___x_2608_ = lean_box(0);
                            v_isShared_2609_ = v_isSharedCheck_2613_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_inc_ref(v_arg_2530_);
                        lean_dec_ref(v_focusHyp_2555_);
                        lean_dec_ref_known(v_p_2516_, 2);
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2573_);
                    lean_del_object(v___x_2566_);
                    lean_del_object(v___x_2561_);
                    lean_dec_ref(v_focusHyp_2555_);
                    lean_del_object(v___x_2528_);
                    lean_dec(v_uniq_2526_);
                    lean_dec(v_name_2525_);
                    lean_dec_ref_known(v_p_2516_, 2);
                    v_a_2614_ = lean_ctor_get(v___x_2595_, 0);
                    v_isSharedCheck_2621_ = (!lean_is_exclusive(v___x_2595_)) as u8;
                    if v_isSharedCheck_2621_ == 0 {
                        v___x_2616_ = v___x_2595_;
                        v_isShared_2617_ = v_isSharedCheck_2621_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2614_);
                        lean_dec(v___x_2595_);
                        v___x_2616_ = lean_box(0);
                        v_isShared_2617_ = v_isSharedCheck_2621_;
                        state = 14;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_2609_ == 0 {
                    v___x_2611_ = v___x_2608_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
                    v___x_2611_ = v_reuseFailAlloc_2612_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2611_;
            }
            14 => {
                if v_isShared_2617_ == 0 {
                    v___x_2619_ = v___x_2616_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
                    v___x_2619_ = v_reuseFailAlloc_2620_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2619_;
            }
            16 => {
                if v_isShared_2641_ == 0 {
                    v___x_2643_ = v___x_2640_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
                    v___x_2643_ = v_reuseFailAlloc_2644_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2643_;
            }
            18 => {
                if v_isShared_2651_ == 0 {
                    v___x_2653_ = v___x_2650_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
                    v___x_2653_ = v_reuseFailAlloc_2654_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2653_;
            }
            20 => {
                return v___x_2659_;
            }
            21 => {
                return v___x_2664_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___boxed(
    mut v_P_2671_: *mut LeanObject,
    mut v_QR_2672_: *mut LeanObject,
    mut v_arg_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
    mut v_a_2675_: *mut LeanObject,
    mut v_a_2676_: *mut LeanObject,
    mut v_a_2677_: *mut LeanObject,
    mut v_a_2678_: *mut LeanObject,
    mut v_a_2679_: *mut LeanObject,
    mut v_a_2680_: *mut LeanObject,
    mut v_a_2681_: *mut LeanObject,
    mut v_a_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2683_: *mut LeanObject = core::ptr::null_mut();
    v_res_2683_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(
        v_P_2671_,
        v_QR_2672_,
        v_arg_2673_,
        v_a_2674_,
        v_a_2675_,
        v_a_2676_,
        v_a_2677_,
        v_a_2678_,
        v_a_2679_,
        v_a_2680_,
        v_a_2681_,
    );
    lean_dec(v_a_2681_);
    lean_dec_ref(v_a_2680_);
    lean_dec(v_a_2679_);
    lean_dec_ref(v_a_2678_);
    lean_dec(v_a_2677_);
    lean_dec_ref(v_a_2676_);
    lean_dec(v_a_2675_);
    lean_dec_ref(v_a_2674_);
    return v_res_2683_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(
    mut v_00_u03b1_2684_: *mut LeanObject,
    mut v_msg_2685_: *mut LeanObject,
    mut v___y_2686_: *mut LeanObject,
    mut v___y_2687_: *mut LeanObject,
    mut v___y_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
    mut v___y_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    v___x_2695_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v_msg_2685_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
    return v___x_2695_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___boxed(
    mut v_00_u03b1_2696_: *mut LeanObject,
    mut v_msg_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
    mut v___y_2701_: *mut LeanObject,
    mut v___y_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
    mut v___y_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2707_: *mut LeanObject = core::ptr::null_mut();
    v_res_2707_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0(
            v_00_u03b1_2696_,
            v_msg_2697_,
            v___y_2698_,
            v___y_2699_,
            v___y_2700_,
            v___y_2701_,
            v___y_2702_,
            v___y_2703_,
            v___y_2704_,
            v___y_2705_,
        );
    lean_dec(v___y_2705_);
    lean_dec_ref(v___y_2704_);
    lean_dec(v___y_2703_);
    lean_dec_ref(v___y_2702_);
    lean_dec(v___y_2701_);
    lean_dec_ref(v___y_2700_);
    lean_dec(v___y_2699_);
    lean_dec_ref(v___y_2698_);
    return v_res_2707_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(
    mut v_cls_2708_: *mut LeanObject,
    mut v_msg_2709_: *mut LeanObject,
    mut v___y_2710_: *mut LeanObject,
    mut v___y_2711_: *mut LeanObject,
    mut v___y_2712_: *mut LeanObject,
    mut v___y_2713_: *mut LeanObject,
    mut v___y_2714_: *mut LeanObject,
    mut v___y_2715_: *mut LeanObject,
    mut v___y_2716_: *mut LeanObject,
    mut v___y_2717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    v___x_2719_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v_cls_2708_, v_msg_2709_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
    return v___x_2719_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___boxed(
    mut v_cls_2720_: *mut LeanObject,
    mut v_msg_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
    mut v___y_2724_: *mut LeanObject,
    mut v___y_2725_: *mut LeanObject,
    mut v___y_2726_: *mut LeanObject,
    mut v___y_2727_: *mut LeanObject,
    mut v___y_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2731_: *mut LeanObject = core::ptr::null_mut();
    v_res_2731_ =
        l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1(
            v_cls_2720_,
            v_msg_2721_,
            v___y_2722_,
            v___y_2723_,
            v___y_2724_,
            v___y_2725_,
            v___y_2726_,
            v___y_2727_,
            v___y_2728_,
            v___y_2729_,
        );
    lean_dec(v___y_2729_);
    lean_dec_ref(v___y_2728_);
    lean_dec(v___y_2727_);
    lean_dec_ref(v___y_2726_);
    lean_dec(v___y_2725_);
    lean_dec_ref(v___y_2724_);
    lean_dec(v___y_2723_);
    lean_dec_ref(v___y_2722_);
    return v_res_2731_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    v___x_2732_ = l_instMonadEIO(lean_box(0));
    return v___x_2732_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(
    mut v_msg_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
    mut v___y_2744_: *mut LeanObject,
    mut v___y_2745_: *mut LeanObject,
    mut v___y_2746_: *mut LeanObject,
    mut v___y_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2754_: u8 = 0;
    let mut v_toFunctor_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2761_: u8 = 0;
    let mut v___f_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2778_: u8 = 0;
    let mut v_toFunctor_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2785_: u8 = 0;
    let mut v___f_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v_toFunctor_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2809_: u8 = 0;
    let mut v___f_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10930__overap_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut v_unused_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut v_unused_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2835_: u8 = 0;
    let mut v_unused_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2837_: u8 = 0;
    let mut v_unused_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut v_unused_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2843_: u8 = 0;
    let mut v_unused_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2749_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0_once), _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__0);
                v___x_2750_ = l_StateRefT_x27_instMonad___redArg(v___x_2749_);
                v_toApplicative_2751_ = lean_ctor_get(v___x_2750_, 0);
                v_isSharedCheck_2843_ = (!lean_is_exclusive(v___x_2750_)) as u8;
                if v_isSharedCheck_2843_ == 0 {
                    v_unused_2844_ = lean_ctor_get(v___x_2750_, 1);
                    lean_dec(v_unused_2844_);
                    v___x_2753_ = v___x_2750_;
                    v_isShared_2754_ = v_isSharedCheck_2843_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2751_);
                    lean_dec(v___x_2750_);
                    v___x_2753_ = lean_box(0);
                    v_isShared_2754_ = v_isSharedCheck_2843_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2755_ = lean_ctor_get(v_toApplicative_2751_, 0);
                v_toSeq_2756_ = lean_ctor_get(v_toApplicative_2751_, 2);
                v_toSeqLeft_2757_ = lean_ctor_get(v_toApplicative_2751_, 3);
                v_toSeqRight_2758_ = lean_ctor_get(v_toApplicative_2751_, 4);
                v_isSharedCheck_2841_ = (!lean_is_exclusive(v_toApplicative_2751_)) as u8;
                if v_isSharedCheck_2841_ == 0 {
                    v_unused_2842_ = lean_ctor_get(v_toApplicative_2751_, 1);
                    lean_dec(v_unused_2842_);
                    v___x_2760_ = v_toApplicative_2751_;
                    v_isShared_2761_ = v_isSharedCheck_2841_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2758_);
                    lean_inc(v_toSeqLeft_2757_);
                    lean_inc(v_toSeq_2756_);
                    lean_inc(v_toFunctor_2755_);
                    lean_dec(v_toApplicative_2751_);
                    v___x_2760_ = lean_box(0);
                    v_isShared_2761_ = v_isSharedCheck_2841_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2762_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__1;
                v___f_2763_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_2755_);
                v___f_2764_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2764_, 0, v_toFunctor_2755_);
                v___f_2765_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2765_, 0, v_toFunctor_2755_);
                v___x_2766_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2766_, 0, v___f_2764_);
                lean_ctor_set(v___x_2766_, 1, v___f_2765_);
                v___f_2767_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2767_, 0, v_toSeqRight_2758_);
                v___f_2768_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2768_, 0, v_toSeqLeft_2757_);
                v___f_2769_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2769_, 0, v_toSeq_2756_);
                if v_isShared_2761_ == 0 {
                    lean_ctor_set(v___x_2760_, 4, v___f_2767_);
                    lean_ctor_set(v___x_2760_, 3, v___f_2768_);
                    lean_ctor_set(v___x_2760_, 2, v___f_2769_);
                    lean_ctor_set(v___x_2760_, 1, v___f_2762_);
                    lean_ctor_set(v___x_2760_, 0, v___x_2766_);
                    v___x_2771_ = v___x_2760_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2766_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 1, v___f_2762_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 2, v___f_2769_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 3, v___f_2768_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 4, v___f_2767_);
                    v___x_2771_ = v_reuseFailAlloc_2840_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2754_ == 0 {
                    lean_ctor_set(v___x_2753_, 1, v___f_2763_);
                    lean_ctor_set(v___x_2753_, 0, v___x_2771_);
                    v___x_2773_ = v___x_2753_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2771_);
                    lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___f_2763_);
                    v___x_2773_ = v_reuseFailAlloc_2839_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2774_ = l_StateRefT_x27_instMonad___redArg(v___x_2773_);
                v_toApplicative_2775_ = lean_ctor_get(v___x_2774_, 0);
                v_isSharedCheck_2837_ = (!lean_is_exclusive(v___x_2774_)) as u8;
                if v_isSharedCheck_2837_ == 0 {
                    v_unused_2838_ = lean_ctor_get(v___x_2774_, 1);
                    lean_dec(v_unused_2838_);
                    v___x_2777_ = v___x_2774_;
                    v_isShared_2778_ = v_isSharedCheck_2837_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2775_);
                    lean_dec(v___x_2774_);
                    v___x_2777_ = lean_box(0);
                    v_isShared_2778_ = v_isSharedCheck_2837_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2779_ = lean_ctor_get(v_toApplicative_2775_, 0);
                v_toSeq_2780_ = lean_ctor_get(v_toApplicative_2775_, 2);
                v_toSeqLeft_2781_ = lean_ctor_get(v_toApplicative_2775_, 3);
                v_toSeqRight_2782_ = lean_ctor_get(v_toApplicative_2775_, 4);
                v_isSharedCheck_2835_ = (!lean_is_exclusive(v_toApplicative_2775_)) as u8;
                if v_isSharedCheck_2835_ == 0 {
                    v_unused_2836_ = lean_ctor_get(v_toApplicative_2775_, 1);
                    lean_dec(v_unused_2836_);
                    v___x_2784_ = v_toApplicative_2775_;
                    v_isShared_2785_ = v_isSharedCheck_2835_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2782_);
                    lean_inc(v_toSeqLeft_2781_);
                    lean_inc(v_toSeq_2780_);
                    lean_inc(v_toFunctor_2779_);
                    lean_dec(v_toApplicative_2775_);
                    v___x_2784_ = lean_box(0);
                    v_isShared_2785_ = v_isSharedCheck_2835_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2786_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__3;
                v___f_2787_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__4;
                lean_inc_ref(v_toFunctor_2779_);
                v___f_2788_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2788_, 0, v_toFunctor_2779_);
                v___f_2789_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2789_, 0, v_toFunctor_2779_);
                v___x_2790_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2790_, 0, v___f_2788_);
                lean_ctor_set(v___x_2790_, 1, v___f_2789_);
                v___f_2791_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2791_, 0, v_toSeqRight_2782_);
                v___f_2792_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2792_, 0, v_toSeqLeft_2781_);
                v___f_2793_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2793_, 0, v_toSeq_2780_);
                if v_isShared_2785_ == 0 {
                    lean_ctor_set(v___x_2784_, 4, v___f_2791_);
                    lean_ctor_set(v___x_2784_, 3, v___f_2792_);
                    lean_ctor_set(v___x_2784_, 2, v___f_2793_);
                    lean_ctor_set(v___x_2784_, 1, v___f_2786_);
                    lean_ctor_set(v___x_2784_, 0, v___x_2790_);
                    v___x_2795_ = v___x_2784_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 1, v___f_2786_);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 2, v___f_2793_);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 3, v___f_2792_);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 4, v___f_2791_);
                    v___x_2795_ = v_reuseFailAlloc_2834_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2778_ == 0 {
                    lean_ctor_set(v___x_2777_, 1, v___f_2787_);
                    lean_ctor_set(v___x_2777_, 0, v___x_2795_);
                    v___x_2797_ = v___x_2777_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2795_);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___f_2787_);
                    v___x_2797_ = v_reuseFailAlloc_2833_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2798_ = l_StateRefT_x27_instMonad___redArg(v___x_2797_);
                v_toApplicative_2799_ = lean_ctor_get(v___x_2798_, 0);
                v_isSharedCheck_2831_ = (!lean_is_exclusive(v___x_2798_)) as u8;
                if v_isSharedCheck_2831_ == 0 {
                    v_unused_2832_ = lean_ctor_get(v___x_2798_, 1);
                    lean_dec(v_unused_2832_);
                    v___x_2801_ = v___x_2798_;
                    v_isShared_2802_ = v_isSharedCheck_2831_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2799_);
                    lean_dec(v___x_2798_);
                    v___x_2801_ = lean_box(0);
                    v_isShared_2802_ = v_isSharedCheck_2831_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_toFunctor_2803_ = lean_ctor_get(v_toApplicative_2799_, 0);
                v_toSeq_2804_ = lean_ctor_get(v_toApplicative_2799_, 2);
                v_toSeqLeft_2805_ = lean_ctor_get(v_toApplicative_2799_, 3);
                v_toSeqRight_2806_ = lean_ctor_get(v_toApplicative_2799_, 4);
                v_isSharedCheck_2829_ = (!lean_is_exclusive(v_toApplicative_2799_)) as u8;
                if v_isSharedCheck_2829_ == 0 {
                    v_unused_2830_ = lean_ctor_get(v_toApplicative_2799_, 1);
                    lean_dec(v_unused_2830_);
                    v___x_2808_ = v_toApplicative_2799_;
                    v_isShared_2809_ = v_isSharedCheck_2829_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2806_);
                    lean_inc(v_toSeqLeft_2805_);
                    lean_inc(v_toSeq_2804_);
                    lean_inc(v_toFunctor_2803_);
                    lean_dec(v_toApplicative_2799_);
                    v___x_2808_ = lean_box(0);
                    v_isShared_2809_ = v_isSharedCheck_2829_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___f_2810_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__5;
                v___f_2811_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___closed__6;
                lean_inc_ref(v_toFunctor_2803_);
                v___f_2812_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2812_, 0, v_toFunctor_2803_);
                v___f_2813_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2813_, 0, v_toFunctor_2803_);
                v___x_2814_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2814_, 0, v___f_2812_);
                lean_ctor_set(v___x_2814_, 1, v___f_2813_);
                v___f_2815_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2815_, 0, v_toSeqRight_2806_);
                v___f_2816_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2816_, 0, v_toSeqLeft_2805_);
                v___f_2817_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2817_, 0, v_toSeq_2804_);
                if v_isShared_2809_ == 0 {
                    lean_ctor_set(v___x_2808_, 4, v___f_2815_);
                    lean_ctor_set(v___x_2808_, 3, v___f_2816_);
                    lean_ctor_set(v___x_2808_, 2, v___f_2817_);
                    lean_ctor_set(v___x_2808_, 1, v___f_2810_);
                    lean_ctor_set(v___x_2808_, 0, v___x_2814_);
                    v___x_2819_ = v___x_2808_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2814_);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 1, v___f_2810_);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 2, v___f_2817_);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 3, v___f_2816_);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 4, v___f_2815_);
                    v___x_2819_ = v_reuseFailAlloc_2828_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2802_ == 0 {
                    lean_ctor_set(v___x_2801_, 1, v___f_2811_);
                    lean_ctor_set(v___x_2801_, 0, v___x_2819_);
                    v___x_2821_ = v___x_2801_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2819_);
                    lean_ctor_set(v_reuseFailAlloc_2827_, 1, v___f_2811_);
                    v___x_2821_ = v_reuseFailAlloc_2827_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2822_ = l_StateRefT_x27_instMonad___redArg(v___x_2821_);
                v___x_2823_ =
                    lean_alloc_closure(l_ReaderT_pure___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___x_2823_, 0, lean_box(0));
                lean_closure_set(v___x_2823_, 1, lean_box(0));
                lean_closure_set(v___x_2823_, 2, v___x_2822_);
                v___x_2824_ = l_OptionT_instInhabitedOfPure___redArg(v___x_2823_);
                v___x_10930__overap_2825_ = lean_panic_fn_borrowed(v___x_2824_, v_msg_2739_);
                lean_dec(v___x_2824_);
                lean_inc(v___y_2747_);
                lean_inc_ref(v___y_2746_);
                lean_inc(v___y_2745_);
                lean_inc_ref(v___y_2744_);
                lean_inc(v___y_2743_);
                lean_inc_ref(v___y_2742_);
                lean_inc(v___y_2741_);
                lean_inc_ref(v___y_2740_);
                v___x_2826_ = lean_apply_9(
                    v___x_10930__overap_2825_,
                    v___y_2740_,
                    v___y_2741_,
                    v___y_2742_,
                    v___y_2743_,
                    v___y_2744_,
                    v___y_2745_,
                    v___y_2746_,
                    v___y_2747_,
                    lean_box(0),
                );
                return v___x_2826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0___boxed(
    mut v_msg_2845_: *mut LeanObject,
    mut v___y_2846_: *mut LeanObject,
    mut v___y_2847_: *mut LeanObject,
    mut v___y_2848_: *mut LeanObject,
    mut v___y_2849_: *mut LeanObject,
    mut v___y_2850_: *mut LeanObject,
    mut v___y_2851_: *mut LeanObject,
    mut v___y_2852_: *mut LeanObject,
    mut v___y_2853_: *mut LeanObject,
    mut v___y_2854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2855_: *mut LeanObject = core::ptr::null_mut();
    v_res_2855_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(
        v_msg_2845_,
        v___y_2846_,
        v___y_2847_,
        v___y_2848_,
        v___y_2849_,
        v___y_2850_,
        v___y_2851_,
        v___y_2852_,
        v___y_2853_,
    );
    lean_dec(v___y_2853_);
    lean_dec_ref(v___y_2852_);
    lean_dec(v___y_2851_);
    lean_dec_ref(v___y_2850_);
    lean_dec(v___y_2849_);
    lean_dec_ref(v___y_2848_);
    lean_dec(v___y_2847_);
    lean_dec_ref(v___y_2846_);
    return v_res_2855_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0()
-> *mut LeanObject {
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    v___x_2856_ = lean_box(0);
    v___x_2857_ = l_Lean_mkSort(v___x_2856_);
    return v___x_2857_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1()
-> *mut LeanObject {
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    v___x_2858_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__0,
    );
    v___x_2859_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2859_, 0, v___x_2858_);
    return v___x_2859_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10()
-> *mut LeanObject {
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    v___x_2885_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__9;
    v___x_2886_ = l_Lean_stringToMessageData(v___x_2885_);
    return v___x_2886_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18()
-> *mut LeanObject {
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    v___x_2905_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__17;
    v___x_2906_ = lean_unsigned_to_nat(37);
    v___x_2907_ = lean_unsigned_to_nat(45);
    v___x_2908_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__16;
    v___x_2909_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15;
    v___x_2910_ = l_mkPanicMessageWithDecl(
        v___x_2909_,
        v___x_2908_,
        v___x_2907_,
        v___x_2906_,
        v___x_2905_,
    );
    return v___x_2910_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(
    mut v_P_2911_: *mut LeanObject,
    mut v_QR_2912_: *mut LeanObject,
    mut v_arg_2913_: *mut LeanObject,
    mut v_a_2914_: *mut LeanObject,
    mut v_a_2915_: *mut LeanObject,
    mut v_a_2916_: *mut LeanObject,
    mut v_a_2917_: *mut LeanObject,
    mut v_a_2918_: *mut LeanObject,
    mut v_a_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2930_: u8 = 0;
    let mut v_p_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uniq_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2936_: u8 = 0;
    let mut v_fn_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: u8 = 0;
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: u8 = 0;
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v_tail_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u8 = 0;
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2987_: u8 = 0;
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c6_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_u03c6_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v_val_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3013_: u8 = 0;
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3037_: u8 = 0;
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut v_reuseFailAlloc_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3054_: u8 = 0;
    let mut v_a_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3058_: u8 = 0;
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3062_: u8 = 0;
    let mut v_val_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut v_a_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___y_3084_: u8 = 0;
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: u8 = 0;
    let mut v_isSharedCheck_3093_: u8 = 0;
    let mut v_a_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut v_unused_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3104_: u8 = 0;
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2926_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_QR_2912_);
                if lean_obj_tag(v___x_2926_) == 1 {
                    v_val_2927_ = lean_ctor_get(v___x_2926_, 0);
                    v_isSharedCheck_3104_ = (!lean_is_exclusive(v___x_2926_)) as u8;
                    if v_isSharedCheck_3104_ == 0 {
                        v___x_2929_ = v___x_2926_;
                        v_isShared_2930_ = v_isSharedCheck_3104_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2927_);
                        lean_dec(v___x_2926_);
                        v___x_2929_ = lean_box(0);
                        v_isShared_2930_ = v_isSharedCheck_3104_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2926_);
                    lean_dec(v_arg_2913_);
                    lean_dec_ref(v_P_2911_);
                    v___x_3105_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__18,
                    );
                    v___x_3106_ =
                        l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(
                            v___x_3105_,
                            v_a_2914_,
                            v_a_2915_,
                            v_a_2916_,
                            v_a_2917_,
                            v_a_2918_,
                            v_a_2919_,
                            v_a_2920_,
                            v_a_2921_,
                        );
                    return v___x_3106_;
                }
            }
            1 => {
                v___x_2924_ = lean_box(0);
                v___x_2925_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2925_, 0, v___x_2924_);
                return v___x_2925_;
            }
            2 => {
                v_p_2931_ = lean_ctor_get(v_val_2927_, 2);
                lean_inc_ref(v_p_2931_);
                if lean_obj_tag(v_p_2931_) == 5 {
                    v_name_2932_ = lean_ctor_get(v_val_2927_, 0);
                    v_uniq_2933_ = lean_ctor_get(v_val_2927_, 1);
                    v_isSharedCheck_3102_ = (!lean_is_exclusive(v_val_2927_)) as u8;
                    if v_isSharedCheck_3102_ == 0 {
                        v_unused_3103_ = lean_ctor_get(v_val_2927_, 2);
                        lean_dec(v_unused_3103_);
                        v___x_2935_ = v_val_2927_;
                        v_isShared_2936_ = v_isSharedCheck_3102_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_uniq_2933_);
                        lean_inc(v_name_2932_);
                        lean_dec(v_val_2927_);
                        v___x_2935_ = lean_box(0);
                        v_isShared_2936_ = v_isSharedCheck_3102_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_2931_);
                    lean_del_object(v___x_2929_);
                    lean_dec(v_val_2927_);
                    lean_dec(v_arg_2913_);
                    lean_dec_ref(v_P_2911_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_fn_2937_ = lean_ctor_get(v_p_2931_, 0);
                v_arg_2938_ = lean_ctor_get(v_p_2931_, 1);
                lean_inc_ref(v_arg_2938_);
                if lean_obj_tag(v_fn_2937_) == 5 {
                    v_fn_2950_ = lean_ctor_get(v_fn_2937_, 0);
                    if lean_obj_tag(v_fn_2950_) == 5 {
                        v_fn_2951_ = lean_ctor_get(v_fn_2950_, 0);
                        if lean_obj_tag(v_fn_2951_) == 4 {
                            v_declName_2952_ = lean_ctor_get(v_fn_2951_, 0);
                            if lean_obj_tag(v_declName_2952_) == 1 {
                                v_pre_2953_ = lean_ctor_get(v_declName_2952_, 0);
                                if lean_obj_tag(v_pre_2953_) == 1 {
                                    v_pre_2954_ = lean_ctor_get(v_pre_2953_, 0);
                                    if lean_obj_tag(v_pre_2954_) == 1 {
                                        v_pre_2955_ = lean_ctor_get(v_pre_2954_, 0);
                                        if lean_obj_tag(v_pre_2955_) == 1 {
                                            v_pre_2956_ = lean_ctor_get(v_pre_2955_, 0);
                                            if lean_obj_tag(v_pre_2956_) == 0 {
                                                v_arg_2957_ = lean_ctor_get(v_fn_2937_, 1);
                                                lean_inc_ref(v_arg_2957_);
                                                v_arg_2958_ = lean_ctor_get(v_fn_2950_, 1);
                                                lean_inc_ref(v_arg_2958_);
                                                v_us_2959_ = lean_ctor_get(v_fn_2951_, 1);
                                                v_str_2960_ = lean_ctor_get(v_declName_2952_, 1);
                                                v_str_2961_ = lean_ctor_get(v_pre_2953_, 1);
                                                v_str_2962_ = lean_ctor_get(v_pre_2954_, 1);
                                                v_str_2963_ = lean_ctor_get(v_pre_2955_, 1);
                                                v___x_2964_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0;
                                                v___x_2965_ =
                                                    lean_string_dec_eq(v_str_2963_, v___x_2964_);
                                                if v___x_2965_ == 0 {
                                                    lean_dec_ref(v_arg_2958_);
                                                    lean_dec_ref(v_arg_2957_);
                                                    lean_dec_ref(v_arg_2938_);
                                                    lean_del_object(v___x_2935_);
                                                    lean_dec(v_uniq_2933_);
                                                    lean_dec_ref_known(v_p_2931_, 2);
                                                    lean_dec(v_name_2932_);
                                                    lean_del_object(v___x_2929_);
                                                    lean_dec(v_arg_2913_);
                                                    lean_dec_ref(v_P_2911_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_2966_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                                                    v___x_2967_ = lean_string_dec_eq(
                                                        v_str_2962_,
                                                        v___x_2966_,
                                                    );
                                                    if v___x_2967_ == 0 {
                                                        lean_dec_ref(v_arg_2958_);
                                                        lean_dec_ref(v_arg_2957_);
                                                        lean_dec_ref(v_arg_2938_);
                                                        lean_del_object(v___x_2935_);
                                                        lean_dec(v_uniq_2933_);
                                                        lean_dec_ref_known(v_p_2931_, 2);
                                                        lean_dec(v_name_2932_);
                                                        lean_del_object(v___x_2929_);
                                                        lean_dec(v_arg_2913_);
                                                        lean_dec_ref(v_P_2911_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_2968_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1;
                                                        v___x_2969_ = lean_string_dec_eq(
                                                            v_str_2961_,
                                                            v___x_2968_,
                                                        );
                                                        if v___x_2969_ == 0 {
                                                            lean_dec_ref(v_arg_2958_);
                                                            lean_dec_ref(v_arg_2957_);
                                                            lean_dec_ref(v_arg_2938_);
                                                            lean_del_object(v___x_2935_);
                                                            lean_dec(v_uniq_2933_);
                                                            lean_dec_ref_known(v_p_2931_, 2);
                                                            lean_dec(v_name_2932_);
                                                            lean_del_object(v___x_2929_);
                                                            lean_dec(v_arg_2913_);
                                                            lean_dec_ref(v_P_2911_);
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_2970_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__2;
                                                            v___x_2971_ = lean_string_dec_eq(
                                                                v_str_2960_,
                                                                v___x_2970_,
                                                            );
                                                            if v___x_2971_ == 0 {
                                                                lean_dec_ref(v_arg_2958_);
                                                                lean_dec_ref(v_arg_2957_);
                                                                lean_dec_ref(v_arg_2938_);
                                                                lean_del_object(v___x_2935_);
                                                                lean_dec(v_uniq_2933_);
                                                                lean_dec_ref_known(v_p_2931_, 2);
                                                                lean_dec(v_name_2932_);
                                                                lean_del_object(v___x_2929_);
                                                                lean_dec(v_arg_2913_);
                                                                lean_dec_ref(v_P_2911_);
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                if lean_obj_tag(v_us_2959_) == 1 {
                                                                    v_tail_2972_ = lean_ctor_get(
                                                                        v_us_2959_, 1,
                                                                    );
                                                                    if lean_obj_tag(v_tail_2972_)
                                                                        == 0
                                                                    {
                                                                        v_head_2973_ =
                                                                            lean_ctor_get(
                                                                                v_us_2959_, 0,
                                                                            );
                                                                        lean_inc(v_head_2973_);
                                                                        v___x_2974_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__1);
                                                                        v___x_2975_ = 0;
                                                                        v___x_2976_ = l_Lean_Meta_mkFreshExprMVar(v___x_2974_, v___x_2975_, v_pre_2956_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
                                                                        if lean_obj_tag(v___x_2976_)
                                                                            == 0
                                                                        {
                                                                            v_a_2977_ =
                                                                                lean_ctor_get(
                                                                                    v___x_2976_,
                                                                                    0,
                                                                                );
                                                                            lean_inc_n(
                                                                                v_a_2977_, 2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v___x_2976_,
                                                                                1,
                                                                            );
                                                                            v___x_2978_ =
                                                                                lean_alloc_ctor(
                                                                                    1,
                                                                                    1,
                                                                                    (0) as u32,
                                                                                );
                                                                            lean_ctor_set(
                                                                                v___x_2978_,
                                                                                0,
                                                                                v_a_2977_,
                                                                            );
                                                                            v___x_2979_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2;
                                                                            v___x_2980_ =
                                                                                lean_box(0);
                                                                            v___x_2981_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_arg_2913_, v___x_2978_, v___x_2979_, v___x_2971_, v___x_2980_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
                                                                            if lean_obj_tag(
                                                                                v___x_2981_,
                                                                            ) == 0
                                                                            {
                                                                                v_a_2982_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_2981_,
                                                                                        0,
                                                                                    );
                                                                                lean_inc(v_a_2982_);
                                                                                lean_dec_ref_known(
                                                                                    v___x_2981_,
                                                                                    1,
                                                                                );
                                                                                v_fst_2983_ =
                                                                                    lean_ctor_get(
                                                                                        v_a_2982_,
                                                                                        0,
                                                                                    );
                                                                                v_snd_2984_ =
                                                                                    lean_ctor_get(
                                                                                        v_a_2982_,
                                                                                        1,
                                                                                    );
                                                                                v_isSharedCheck_3078_ = (!lean_is_exclusive(v_a_2982_)) as u8;
                                                                                if v_isSharedCheck_3078_ == 0 {
v___x_2986_ = v_a_2982_;
v_isShared_2987_ = v_isSharedCheck_3078_;
state = 7; continue;
} else {
lean_inc(v_snd_2984_);
lean_inc(v_fst_2983_);
lean_dec(v_a_2982_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3078_;
state = 7; continue;
}
                                                                            } else {
                                                                                lean_dec(v_a_2977_);
                                                                                lean_dec(
                                                                                    v_head_2973_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_2958_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_2957_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_2938_,
                                                                                );
                                                                                lean_del_object(
                                                                                    v___x_2935_,
                                                                                );
                                                                                lean_dec(
                                                                                    v_uniq_2933_,
                                                                                );
                                                                                lean_dec(
                                                                                    v_name_2932_,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_p_2931_, 2,
                                                                                );
                                                                                lean_del_object(
                                                                                    v___x_2929_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_P_2911_,
                                                                                );
                                                                                v_a_3079_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_2981_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_3093_ = (!lean_is_exclusive(v___x_2981_)) as u8;
                                                                                if v_isSharedCheck_3093_ == 0 {
v___x_3081_ = v___x_2981_;
v_isShared_3082_ = v_isSharedCheck_3093_;
state = 20; continue;
} else {
lean_inc(v_a_3079_);
lean_dec(v___x_2981_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3093_;
state = 20; continue;
}
                                                                            }
                                                                        } else {
                                                                            lean_dec(v_head_2973_);
                                                                            lean_dec_ref(
                                                                                v_arg_2958_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_2957_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_2938_,
                                                                            );
                                                                            lean_del_object(
                                                                                v___x_2935_,
                                                                            );
                                                                            lean_dec(v_uniq_2933_);
                                                                            lean_dec_ref_known(
                                                                                v_p_2931_, 2,
                                                                            );
                                                                            lean_dec(v_name_2932_);
                                                                            lean_del_object(
                                                                                v___x_2929_,
                                                                            );
                                                                            lean_dec(v_arg_2913_);
                                                                            lean_dec_ref(v_P_2911_);
                                                                            v_a_3094_ =
                                                                                lean_ctor_get(
                                                                                    v___x_2976_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_3101_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_2976_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_3101_
                                                                                == 0
                                                                            {
                                                                                v___x_3096_ =
                                                                                    v___x_2976_;
                                                                                v_isShared_3097_ = v_isSharedCheck_3101_;
                                                                                state = 24;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_3094_);
                                                                                lean_dec(
                                                                                    v___x_2976_,
                                                                                );
                                                                                v___x_3096_ =
                                                                                    lean_box(0);
                                                                                v_isShared_3097_ = v_isSharedCheck_3101_;
                                                                                state = 24;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_2958_);
                                                                        lean_dec_ref(v_arg_2957_);
                                                                        lean_dec_ref(v_arg_2938_);
                                                                        lean_del_object(
                                                                            v___x_2935_,
                                                                        );
                                                                        lean_dec(v_uniq_2933_);
                                                                        lean_dec_ref_known(
                                                                            v_p_2931_, 2,
                                                                        );
                                                                        lean_dec(v_name_2932_);
                                                                        lean_del_object(
                                                                            v___x_2929_,
                                                                        );
                                                                        lean_dec(v_arg_2913_);
                                                                        lean_dec_ref(v_P_2911_);
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_arg_2958_);
                                                                    lean_dec_ref(v_arg_2957_);
                                                                    lean_dec_ref(v_arg_2938_);
                                                                    lean_del_object(v___x_2935_);
                                                                    lean_dec(v_uniq_2933_);
                                                                    lean_dec_ref_known(
                                                                        v_p_2931_, 2,
                                                                    );
                                                                    lean_dec(v_name_2932_);
                                                                    lean_del_object(v___x_2929_);
                                                                    lean_dec(v_arg_2913_);
                                                                    lean_dec_ref(v_P_2911_);
                                                                    state = 1;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_2938_);
                                                lean_del_object(v___x_2935_);
                                                lean_dec(v_uniq_2933_);
                                                lean_dec_ref_known(v_p_2931_, 2);
                                                lean_dec(v_name_2932_);
                                                lean_del_object(v___x_2929_);
                                                lean_dec(v_arg_2913_);
                                                lean_dec_ref(v_P_2911_);
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_2938_);
                                            lean_del_object(v___x_2935_);
                                            lean_dec(v_uniq_2933_);
                                            lean_dec_ref_known(v_p_2931_, 2);
                                            lean_dec(v_name_2932_);
                                            lean_del_object(v___x_2929_);
                                            lean_dec(v_arg_2913_);
                                            lean_dec_ref(v_P_2911_);
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_arg_2938_);
                                        lean_del_object(v___x_2935_);
                                        lean_dec(v_uniq_2933_);
                                        lean_dec_ref_known(v_p_2931_, 2);
                                        lean_dec(v_name_2932_);
                                        lean_del_object(v___x_2929_);
                                        lean_dec(v_arg_2913_);
                                        lean_dec_ref(v_P_2911_);
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_2938_);
                                    lean_del_object(v___x_2935_);
                                    lean_dec(v_uniq_2933_);
                                    lean_dec_ref_known(v_p_2931_, 2);
                                    lean_dec(v_name_2932_);
                                    lean_del_object(v___x_2929_);
                                    lean_dec(v_arg_2913_);
                                    lean_dec_ref(v_P_2911_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_arg_2938_);
                                lean_del_object(v___x_2935_);
                                lean_dec(v_uniq_2933_);
                                lean_dec_ref_known(v_p_2931_, 2);
                                lean_dec(v_name_2932_);
                                lean_del_object(v___x_2929_);
                                lean_dec(v_arg_2913_);
                                lean_dec_ref(v_P_2911_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_arg_2938_);
                            lean_del_object(v___x_2935_);
                            lean_dec(v_uniq_2933_);
                            lean_dec_ref_known(v_p_2931_, 2);
                            lean_dec(v_name_2932_);
                            lean_del_object(v___x_2929_);
                            lean_dec(v_arg_2913_);
                            lean_dec_ref(v_P_2911_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_arg_2938_);
                        lean_del_object(v___x_2935_);
                        lean_dec(v_uniq_2933_);
                        lean_dec_ref_known(v_p_2931_, 2);
                        lean_dec(v_name_2932_);
                        lean_del_object(v___x_2929_);
                        lean_dec(v_arg_2913_);
                        lean_dec_ref(v_P_2911_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_arg_2938_);
                    lean_del_object(v___x_2935_);
                    lean_dec(v_uniq_2933_);
                    lean_dec_ref_known(v_p_2931_, 2);
                    lean_dec(v_name_2932_);
                    lean_del_object(v___x_2929_);
                    lean_dec(v_arg_2913_);
                    lean_dec_ref(v_P_2911_);
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v_isShared_2936_ == 0 {
                    lean_ctor_set(v___x_2935_, 2, v_arg_2938_);
                    v___x_2942_ = v___x_2935_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_name_2932_);
                    lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_uniq_2933_);
                    lean_ctor_set(v_reuseFailAlloc_2949_, 2, v_arg_2938_);
                    v___x_2942_ = v_reuseFailAlloc_2949_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2943_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2942_);
                v___x_2944_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2944_, 0, v___x_2943_);
                lean_ctor_set(v___x_2944_, 1, v___y_2940_);
                if v_isShared_2930_ == 0 {
                    lean_ctor_set(v___x_2929_, 0, v___x_2944_);
                    v___x_2946_ = v___x_2929_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2944_);
                    v___x_2946_ = v_reuseFailAlloc_2948_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2947_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2947_, 0, v___x_2946_);
                return v___x_2947_;
            }
            7 => {
                v___x_2988_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__4;
                lean_inc_ref(v_us_2959_);
                v___x_2989_ = l_Lean_mkConst(v___x_2988_, v_us_2959_);
                lean_inc(v_a_2977_);
                lean_inc_ref(v_arg_2957_);
                lean_inc_ref(v_arg_2958_);
                v___x_2990_ = l_Lean_mkApp3(v___x_2989_, v_arg_2958_, v_arg_2957_, v_a_2977_);
                v___x_2991_ = l_Lean_Meta_synthInstance_x3f(
                    v___x_2990_,
                    v___x_2980_,
                    v_a_2918_,
                    v_a_2919_,
                    v_a_2920_,
                    v_a_2921_,
                );
                if lean_obj_tag(v___x_2991_) == 0 {
                    v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
                    lean_inc(v_a_2992_);
                    lean_dec_ref_known(v___x_2991_, 1);
                    if lean_obj_tag(v_a_2992_) == 1 {
                        v_val_3063_ = lean_ctor_get(v_a_2992_, 0);
                        lean_inc(v_val_3063_);
                        lean_dec_ref_known(v_a_2992_, 1);
                        v___x_3064_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__12;
                        lean_inc_ref_n(v_us_2959_, 2);
                        v___x_3065_ = l_Lean_mkConst(v___x_3064_, v_us_2959_);
                        lean_inc_ref_n(v_arg_2957_, 2);
                        lean_inc_ref_n(v_arg_2958_, 2);
                        v___x_3066_ = l_Lean_mkApp5(
                            v___x_3065_,
                            v_arg_2958_,
                            v_a_2977_,
                            v_arg_2957_,
                            v_val_3063_,
                            v_fst_2983_,
                        );
                        v___x_3067_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__14;
                        v___x_3068_ = l_Lean_mkConst(v___x_3067_, v_us_2959_);
                        v___x_3069_ = l_Lean_mkAppB(v___x_3068_, v_arg_2958_, v_arg_2957_);
                        v_00_u03c6_2994_ = v___x_3069_;
                        v_h_u03c6_2995_ = v___x_3066_;
                        v___y_2996_ = v_a_2915_;
                        v___y_2997_ = v_a_2918_;
                        v___y_2998_ = v_a_2919_;
                        v___y_2999_ = v_a_2920_;
                        v___y_3000_ = v_a_2921_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v_a_2992_);
                        v_00_u03c6_2994_ = v_a_2977_;
                        v_h_u03c6_2995_ = v_fst_2983_;
                        v___y_2996_ = v_a_2915_;
                        v___y_2997_ = v_a_2918_;
                        v___y_2998_ = v_a_2919_;
                        v___y_2999_ = v_a_2920_;
                        v___y_3000_ = v_a_2921_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2986_);
                    lean_dec(v_snd_2984_);
                    lean_dec(v_fst_2983_);
                    lean_dec(v_a_2977_);
                    lean_dec(v_head_2973_);
                    lean_dec_ref(v_arg_2958_);
                    lean_dec_ref(v_arg_2957_);
                    lean_dec_ref(v_arg_2938_);
                    lean_del_object(v___x_2935_);
                    lean_dec(v_uniq_2933_);
                    lean_dec(v_name_2932_);
                    lean_dec_ref_known(v_p_2931_, 2);
                    lean_del_object(v___x_2929_);
                    lean_dec_ref(v_P_2911_);
                    v_a_3070_ = lean_ctor_get(v___x_2991_, 0);
                    v_isSharedCheck_3077_ = (!lean_is_exclusive(v___x_2991_)) as u8;
                    if v_isSharedCheck_3077_ == 0 {
                        v___x_3072_ = v___x_2991_;
                        v_isShared_3073_ = v_isSharedCheck_3077_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_3070_);
                        lean_dec(v___x_2991_);
                        v___x_3072_ = lean_box(0);
                        v_isShared_3073_ = v_isSharedCheck_3077_;
                        state = 18;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3001_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__6;
                lean_inc_ref(v_us_2959_);
                v___x_3002_ = l_Lean_mkConst(v___x_3001_, v_us_2959_);
                lean_inc_ref(v_arg_2957_);
                lean_inc_ref(v_arg_2958_);
                lean_inc_ref(v_00_u03c6_2994_);
                v___x_3003_ =
                    l_Lean_mkApp3(v___x_3002_, v_00_u03c6_2994_, v_arg_2958_, v_arg_2957_);
                v___x_3004_ = l_Lean_Meta_synthInstance_x3f(
                    v___x_3003_,
                    v___x_2980_,
                    v___y_2997_,
                    v___y_2998_,
                    v___y_2999_,
                    v___y_3000_,
                );
                if lean_obj_tag(v___x_3004_) == 0 {
                    v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
                    v_isSharedCheck_3054_ = (!lean_is_exclusive(v___x_3004_)) as u8;
                    if v_isSharedCheck_3054_ == 0 {
                        v___x_3007_ = v___x_3004_;
                        v_isShared_3008_ = v_isSharedCheck_3054_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3005_);
                        lean_dec(v___x_3004_);
                        v___x_3007_ = lean_box(0);
                        v_isShared_3008_ = v_isSharedCheck_3054_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_h_u03c6_2995_);
                    lean_dec_ref(v_00_u03c6_2994_);
                    lean_del_object(v___x_2986_);
                    lean_dec(v_snd_2984_);
                    lean_dec(v_head_2973_);
                    lean_dec_ref(v_arg_2958_);
                    lean_dec_ref(v_arg_2957_);
                    lean_dec_ref(v_arg_2938_);
                    lean_del_object(v___x_2935_);
                    lean_dec(v_uniq_2933_);
                    lean_dec_ref_known(v_p_2931_, 2);
                    lean_dec(v_name_2932_);
                    lean_del_object(v___x_2929_);
                    lean_dec_ref(v_P_2911_);
                    v_a_3055_ = lean_ctor_get(v___x_3004_, 0);
                    v_isSharedCheck_3062_ = (!lean_is_exclusive(v___x_3004_)) as u8;
                    if v_isSharedCheck_3062_ == 0 {
                        v___x_3057_ = v___x_3004_;
                        v_isShared_3058_ = v_isSharedCheck_3062_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_3055_);
                        lean_dec(v___x_3004_);
                        v___x_3057_ = lean_box(0);
                        v_isShared_3058_ = v_isSharedCheck_3062_;
                        state = 16;
                        continue;
                    }
                }
            }
            9 => {
                if lean_obj_tag(v_a_3005_) == 1 {
                    lean_del_object(v___x_3007_);
                    v_val_3009_ = lean_ctor_get(v_a_3005_, 0);
                    lean_inc(v_val_3009_);
                    lean_dec_ref_known(v_a_3005_, 1);
                    v___x_3010_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_2984_, v___y_2996_);
                    if lean_obj_tag(v___x_3010_) == 0 {
                        lean_dec_ref_known(v___x_3010_, 1);
                        v_options_3011_ = lean_ctor_get(v___y_2999_, 2);
                        v_inheritedTraceOptions_3012_ = lean_ctor_get(v___y_2999_, 13);
                        v_hasTrace_3013_ = lean_ctor_get_uint8(
                            v_options_3011_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        v___x_3014_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__8;
                        lean_inc_ref(v_us_2959_);
                        v___x_3015_ = l_Lean_mkConst(v___x_3014_, v_us_2959_);
                        lean_inc_ref(v_arg_2938_);
                        lean_inc_ref(v_arg_2957_);
                        lean_inc_ref(v_P_2911_);
                        lean_inc_ref(v_arg_2958_);
                        v___x_3016_ = l_Lean_mkApp7(
                            v___x_3015_,
                            v_arg_2958_,
                            v_00_u03c6_2994_,
                            v_P_2911_,
                            v_arg_2957_,
                            v_arg_2938_,
                            v_val_3009_,
                            v_h_u03c6_2995_,
                        );
                        if v_hasTrace_3013_ == 0 {
                            lean_del_object(v___x_2986_);
                            lean_dec(v_head_2973_);
                            lean_dec_ref(v_arg_2958_);
                            lean_dec_ref(v_arg_2957_);
                            lean_dec_ref_known(v_p_2931_, 2);
                            lean_dec_ref(v_P_2911_);
                            v___y_2940_ = v___x_3016_;
                            state = 4;
                            continue;
                        } else {
                            v___x_3017_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                            v___x_3018_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
                            v___x_3019_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3012_,
                                v_options_3011_,
                                v___x_3018_,
                            );
                            if v___x_3019_ == 0 {
                                lean_del_object(v___x_2986_);
                                lean_dec(v_head_2973_);
                                lean_dec_ref(v_arg_2958_);
                                lean_dec_ref(v_arg_2957_);
                                lean_dec_ref_known(v_p_2931_, 2);
                                lean_dec_ref(v_P_2911_);
                                v___y_2940_ = v___x_3016_;
                                state = 4;
                                continue;
                            } else {
                                v___x_3020_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__10);
                                v___x_3021_ = l_Lean_MessageData_ofExpr(v_p_2931_);
                                if v_isShared_2987_ == 0 {
                                    lean_ctor_set_tag(v___x_2986_, 7);
                                    lean_ctor_set(v___x_2986_, 1, v___x_3021_);
                                    lean_ctor_set(v___x_2986_, 0, v___x_3020_);
                                    v___x_3023_ = v___x_2986_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3042_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3020_);
                                    lean_ctor_set(v_reuseFailAlloc_3042_, 1, v___x_3021_);
                                    v___x_3023_ = v_reuseFailAlloc_3042_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_3009_);
                        lean_dec_ref(v_h_u03c6_2995_);
                        lean_dec_ref(v_00_u03c6_2994_);
                        lean_del_object(v___x_2986_);
                        lean_dec(v_head_2973_);
                        lean_dec_ref(v_arg_2958_);
                        lean_dec_ref(v_arg_2957_);
                        lean_dec_ref(v_arg_2938_);
                        lean_del_object(v___x_2935_);
                        lean_dec(v_uniq_2933_);
                        lean_dec_ref_known(v_p_2931_, 2);
                        lean_dec(v_name_2932_);
                        lean_del_object(v___x_2929_);
                        lean_dec_ref(v_P_2911_);
                        v_a_3043_ = lean_ctor_get(v___x_3010_, 0);
                        v_isSharedCheck_3050_ = (!lean_is_exclusive(v___x_3010_)) as u8;
                        if v_isSharedCheck_3050_ == 0 {
                            v___x_3045_ = v___x_3010_;
                            v_isShared_3046_ = v_isSharedCheck_3050_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_3043_);
                            lean_dec(v___x_3010_);
                            v___x_3045_ = lean_box(0);
                            v_isShared_3046_ = v_isSharedCheck_3050_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3005_);
                    lean_dec_ref(v_h_u03c6_2995_);
                    lean_dec_ref(v_00_u03c6_2994_);
                    lean_del_object(v___x_2986_);
                    lean_dec(v_snd_2984_);
                    lean_dec(v_head_2973_);
                    lean_dec_ref(v_arg_2958_);
                    lean_dec_ref(v_arg_2957_);
                    lean_dec_ref(v_arg_2938_);
                    lean_del_object(v___x_2935_);
                    lean_dec(v_uniq_2933_);
                    lean_dec_ref_known(v_p_2931_, 2);
                    lean_dec(v_name_2932_);
                    lean_del_object(v___x_2929_);
                    lean_dec_ref(v_P_2911_);
                    if v_isShared_3008_ == 0 {
                        lean_ctor_set(v___x_3007_, 0, v___x_2980_);
                        v___x_3052_ = v___x_3007_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_2980_);
                        v___x_3052_ = v_reuseFailAlloc_3053_;
                        state = 15;
                        continue;
                    }
                }
            }
            10 => {
                v___x_3024_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8,
                );
                v___x_3025_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3025_, 0, v___x_3023_);
                lean_ctor_set(v___x_3025_, 1, v___x_3024_);
                v___x_3026_ = l_Lean_MessageData_ofExpr(v_arg_2957_);
                v___x_3027_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3027_, 0, v___x_3025_);
                lean_ctor_set(v___x_3027_, 1, v___x_3026_);
                v___x_3028_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15,
                );
                v___x_3029_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3029_, 0, v___x_3027_);
                lean_ctor_set(v___x_3029_, 1, v___x_3028_);
                lean_inc_ref(v_arg_2938_);
                v___x_3030_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_head_2973_,
                    v_arg_2958_,
                    v_P_2911_,
                    v_arg_2938_,
                );
                v___x_3031_ = l_Lean_MessageData_ofExpr(v___x_3030_);
                v___x_3032_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3032_, 0, v___x_3029_);
                lean_ctor_set(v___x_3032_, 1, v___x_3031_);
                v___x_3033_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_3017_, v___x_3032_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
                if lean_obj_tag(v___x_3033_) == 0 {
                    lean_dec_ref_known(v___x_3033_, 1);
                    v___y_2940_ = v___x_3016_;
                    state = 4;
                    continue;
                } else {
                    lean_dec_ref(v___x_3016_);
                    lean_dec_ref(v_arg_2938_);
                    lean_del_object(v___x_2935_);
                    lean_dec(v_uniq_2933_);
                    lean_dec(v_name_2932_);
                    lean_del_object(v___x_2929_);
                    v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
                    v_isSharedCheck_3041_ = (!lean_is_exclusive(v___x_3033_)) as u8;
                    if v_isSharedCheck_3041_ == 0 {
                        v___x_3036_ = v___x_3033_;
                        v_isShared_3037_ = v_isSharedCheck_3041_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3034_);
                        lean_dec(v___x_3033_);
                        v___x_3036_ = lean_box(0);
                        v_isShared_3037_ = v_isSharedCheck_3041_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_3037_ == 0 {
                    v___x_3039_ = v___x_3036_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
                    v___x_3039_ = v_reuseFailAlloc_3040_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3039_;
            }
            13 => {
                if v_isShared_3046_ == 0 {
                    v___x_3048_ = v___x_3045_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
                    v___x_3048_ = v_reuseFailAlloc_3049_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3048_;
            }
            15 => {
                return v___x_3052_;
            }
            16 => {
                if v_isShared_3058_ == 0 {
                    v___x_3060_ = v___x_3057_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
                    v___x_3060_ = v_reuseFailAlloc_3061_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3060_;
            }
            18 => {
                if v_isShared_3073_ == 0 {
                    v___x_3075_ = v___x_3072_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
                    v___x_3075_ = v_reuseFailAlloc_3076_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3075_;
            }
            20 => {
                v___x_3091_ = l_Lean_Exception_isInterrupt(v_a_3079_);
                if v___x_3091_ == 0 {
                    lean_inc(v_a_3079_);
                    v___x_3092_ = l_Lean_Exception_isRuntime(v_a_3079_);
                    v___y_3084_ = v___x_3092_;
                    state = 21;
                    continue;
                } else {
                    v___y_3084_ = v___x_3091_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v___y_3084_ == 0 {
                    lean_dec(v_a_3079_);
                    if v_isShared_3082_ == 0 {
                        lean_ctor_set_tag(v___x_3081_, 0);
                        lean_ctor_set(v___x_3081_, 0, v___x_2980_);
                        v___x_3086_ = v___x_3081_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_2980_);
                        v___x_3086_ = v_reuseFailAlloc_3087_;
                        state = 22;
                        continue;
                    }
                } else {
                    if v_isShared_3082_ == 0 {
                        v___x_3089_ = v___x_3081_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3079_);
                        v___x_3089_ = v_reuseFailAlloc_3090_;
                        state = 23;
                        continue;
                    }
                }
            }
            22 => {
                return v___x_3086_;
            }
            23 => {
                return v___x_3089_;
            }
            24 => {
                if v_isShared_3097_ == 0 {
                    v___x_3099_ = v___x_3096_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___boxed(
    mut v_P_3107_: *mut LeanObject,
    mut v_QR_3108_: *mut LeanObject,
    mut v_arg_3109_: *mut LeanObject,
    mut v_a_3110_: *mut LeanObject,
    mut v_a_3111_: *mut LeanObject,
    mut v_a_3112_: *mut LeanObject,
    mut v_a_3113_: *mut LeanObject,
    mut v_a_3114_: *mut LeanObject,
    mut v_a_3115_: *mut LeanObject,
    mut v_a_3116_: *mut LeanObject,
    mut v_a_3117_: *mut LeanObject,
    mut v_a_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3119_: *mut LeanObject = core::ptr::null_mut();
    v_res_3119_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(
        v_P_3107_,
        v_QR_3108_,
        v_arg_3109_,
        v_a_3110_,
        v_a_3111_,
        v_a_3112_,
        v_a_3113_,
        v_a_3114_,
        v_a_3115_,
        v_a_3116_,
        v_a_3117_,
    );
    lean_dec(v_a_3117_);
    lean_dec_ref(v_a_3116_);
    lean_dec(v_a_3115_);
    lean_dec_ref(v_a_3114_);
    lean_dec(v_a_3113_);
    lean_dec_ref(v_a_3112_);
    lean_dec(v_a_3111_);
    lean_dec_ref(v_a_3110_);
    return v_res_3119_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3()
-> *mut LeanObject {
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__2;
    v___x_3130_ = l_Lean_stringToMessageData(v___x_3129_);
    return v___x_3130_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6()
-> *mut LeanObject {
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    v___x_3133_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__5;
    v___x_3134_ = lean_unsigned_to_nat(36);
    v___x_3135_ = lean_unsigned_to_nat(73);
    v___x_3136_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__4;
    v___x_3137_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15;
    v___x_3138_ = l_mkPanicMessageWithDecl(
        v___x_3137_,
        v___x_3136_,
        v___x_3135_,
        v___x_3134_,
        v___x_3133_,
    );
    return v___x_3138_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(
    mut v_P_3139_: *mut LeanObject,
    mut v_00_u03a8_3140_: *mut LeanObject,
    mut v_arg_3141_: *mut LeanObject,
    mut v_a_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
    mut v_a_3145_: *mut LeanObject,
    mut v_a_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
    mut v_a_3148_: *mut LeanObject,
    mut v_a_3149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3158_: u8 = 0;
    let mut v_p_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uniq_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v_arg_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: u8 = 0;
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: u8 = 0;
    let mut v_tail_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3209_: u8 = 0;
    let mut v_options_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3212_: u8 = 0;
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3256_: u8 = 0;
    let mut v_reuseFailAlloc_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3258_: u8 = 0;
    let mut v_unused_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3263_: u8 = 0;
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3267_: u8 = 0;
    let mut v_isSharedCheck_3268_: u8 = 0;
    let mut v_a_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v___y_3274_: u8 = 0;
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: u8 = 0;
    let mut v___x_3282_: u8 = 0;
    let mut v_isSharedCheck_3283_: u8 = 0;
    let mut v_reuseFailAlloc_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v_unused_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_unused_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3289_: u8 = 0;
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3154_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_00_u03a8_3140_);
                if lean_obj_tag(v___x_3154_) == 1 {
                    v_val_3155_ = lean_ctor_get(v___x_3154_, 0);
                    v_isSharedCheck_3289_ = (!lean_is_exclusive(v___x_3154_)) as u8;
                    if v_isSharedCheck_3289_ == 0 {
                        v___x_3157_ = v___x_3154_;
                        v_isShared_3158_ = v_isSharedCheck_3289_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3155_);
                        lean_dec(v___x_3154_);
                        v___x_3157_ = lean_box(0);
                        v_isShared_3158_ = v_isSharedCheck_3289_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3154_);
                    lean_dec(v_arg_3141_);
                    lean_dec_ref(v_P_3139_);
                    v___x_3290_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__6,
                    );
                    v___x_3291_ =
                        l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure_spec__0(
                            v___x_3290_,
                            v_a_3142_,
                            v_a_3143_,
                            v_a_3144_,
                            v_a_3145_,
                            v_a_3146_,
                            v_a_3147_,
                            v_a_3148_,
                            v_a_3149_,
                        );
                    return v___x_3291_;
                }
            }
            1 => {
                v___x_3152_ = lean_box(0);
                v___x_3153_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3153_, 0, v___x_3152_);
                return v___x_3153_;
            }
            2 => {
                v_p_3159_ = lean_ctor_get(v_val_3155_, 2);
                lean_inc_ref(v_p_3159_);
                if lean_obj_tag(v_p_3159_) == 5 {
                    v_fn_3160_ = lean_ctor_get(v_p_3159_, 0);
                    if lean_obj_tag(v_fn_3160_) == 5 {
                        v_fn_3161_ = lean_ctor_get(v_fn_3160_, 0);
                        if lean_obj_tag(v_fn_3161_) == 5 {
                            v_fn_3162_ = lean_ctor_get(v_fn_3161_, 0);
                            if lean_obj_tag(v_fn_3162_) == 4 {
                                v_declName_3163_ = lean_ctor_get(v_fn_3162_, 0);
                                if lean_obj_tag(v_declName_3163_) == 1 {
                                    v_pre_3164_ = lean_ctor_get(v_declName_3163_, 0);
                                    if lean_obj_tag(v_pre_3164_) == 1 {
                                        v_pre_3165_ = lean_ctor_get(v_pre_3164_, 0);
                                        if lean_obj_tag(v_pre_3165_) == 1 {
                                            v_pre_3166_ = lean_ctor_get(v_pre_3165_, 0);
                                            if lean_obj_tag(v_pre_3166_) == 1 {
                                                v_pre_3167_ = lean_ctor_get(v_pre_3166_, 0);
                                                if lean_obj_tag(v_pre_3167_) == 0 {
                                                    v_name_3168_ = lean_ctor_get(v_val_3155_, 0);
                                                    v_uniq_3169_ = lean_ctor_get(v_val_3155_, 1);
                                                    v_isSharedCheck_3287_ =
                                                        (!lean_is_exclusive(v_val_3155_)) as u8;
                                                    if v_isSharedCheck_3287_ == 0 {
                                                        v_unused_3288_ =
                                                            lean_ctor_get(v_val_3155_, 2);
                                                        lean_dec(v_unused_3288_);
                                                        v___x_3171_ = v_val_3155_;
                                                        v_isShared_3172_ = v_isSharedCheck_3287_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_uniq_3169_);
                                                        lean_inc(v_name_3168_);
                                                        lean_dec(v_val_3155_);
                                                        v___x_3171_ = lean_box(0);
                                                        v_isShared_3172_ = v_isSharedCheck_3287_;
                                                        state = 3;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref_known(v_p_3159_, 2);
                                                    lean_del_object(v___x_3157_);
                                                    lean_dec(v_val_3155_);
                                                    lean_dec(v_arg_3141_);
                                                    lean_dec_ref(v_P_3139_);
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref_known(v_p_3159_, 2);
                                                lean_del_object(v___x_3157_);
                                                lean_dec(v_val_3155_);
                                                lean_dec(v_arg_3141_);
                                                lean_dec_ref(v_P_3139_);
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref_known(v_p_3159_, 2);
                                            lean_del_object(v___x_3157_);
                                            lean_dec(v_val_3155_);
                                            lean_dec(v_arg_3141_);
                                            lean_dec_ref(v_P_3139_);
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref_known(v_p_3159_, 2);
                                        lean_del_object(v___x_3157_);
                                        lean_dec(v_val_3155_);
                                        lean_dec(v_arg_3141_);
                                        lean_dec_ref(v_P_3139_);
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_p_3159_, 2);
                                    lean_del_object(v___x_3157_);
                                    lean_dec(v_val_3155_);
                                    lean_dec(v_arg_3141_);
                                    lean_dec_ref(v_P_3139_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_p_3159_, 2);
                                lean_del_object(v___x_3157_);
                                lean_dec(v_val_3155_);
                                lean_dec(v_arg_3141_);
                                lean_dec_ref(v_P_3139_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_p_3159_, 2);
                            lean_del_object(v___x_3157_);
                            lean_dec(v_val_3155_);
                            lean_dec(v_arg_3141_);
                            lean_dec_ref(v_P_3139_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_p_3159_, 2);
                        lean_del_object(v___x_3157_);
                        lean_dec(v_val_3155_);
                        lean_dec(v_arg_3141_);
                        lean_dec_ref(v_P_3139_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_3159_);
                    lean_del_object(v___x_3157_);
                    lean_dec(v_val_3155_);
                    lean_dec(v_arg_3141_);
                    lean_dec_ref(v_P_3139_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_arg_3173_ = lean_ctor_get(v_p_3159_, 1);
                v_arg_3174_ = lean_ctor_get(v_fn_3160_, 1);
                lean_inc_ref(v_arg_3174_);
                v_arg_3175_ = lean_ctor_get(v_fn_3161_, 1);
                v_us_3176_ = lean_ctor_get(v_fn_3162_, 1);
                v_str_3177_ = lean_ctor_get(v_declName_3163_, 1);
                v_str_3178_ = lean_ctor_get(v_pre_3164_, 1);
                v_str_3179_ = lean_ctor_get(v_pre_3165_, 1);
                v_str_3180_ = lean_ctor_get(v_pre_3166_, 1);
                v___x_3181_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0;
                v___x_3182_ = lean_string_dec_eq(v_str_3180_, v___x_3181_);
                if v___x_3182_ == 0 {
                    lean_dec_ref(v_arg_3174_);
                    lean_del_object(v___x_3171_);
                    lean_dec(v_uniq_3169_);
                    lean_dec(v_name_3168_);
                    lean_dec_ref_known(v_p_3159_, 2);
                    lean_del_object(v___x_3157_);
                    lean_dec(v_arg_3141_);
                    lean_dec_ref(v_P_3139_);
                    state = 1;
                    continue;
                } else {
                    v___x_3183_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                    v___x_3184_ = lean_string_dec_eq(v_str_3179_, v___x_3183_);
                    if v___x_3184_ == 0 {
                        lean_dec_ref(v_arg_3174_);
                        lean_del_object(v___x_3171_);
                        lean_dec(v_uniq_3169_);
                        lean_dec(v_name_3168_);
                        lean_dec_ref_known(v_p_3159_, 2);
                        lean_del_object(v___x_3157_);
                        lean_dec(v_arg_3141_);
                        lean_dec_ref(v_P_3139_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3185_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1;
                        v___x_3186_ = lean_string_dec_eq(v_str_3178_, v___x_3185_);
                        if v___x_3186_ == 0 {
                            lean_dec_ref(v_arg_3174_);
                            lean_del_object(v___x_3171_);
                            lean_dec(v_uniq_3169_);
                            lean_dec(v_name_3168_);
                            lean_dec_ref_known(v_p_3159_, 2);
                            lean_del_object(v___x_3157_);
                            lean_dec(v_arg_3141_);
                            lean_dec_ref(v_P_3139_);
                            state = 1;
                            continue;
                        } else {
                            v___x_3187_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__0;
                            v___x_3188_ = lean_string_dec_eq(v_str_3177_, v___x_3187_);
                            if v___x_3188_ == 0 {
                                lean_dec_ref(v_arg_3174_);
                                lean_del_object(v___x_3171_);
                                lean_dec(v_uniq_3169_);
                                lean_dec(v_name_3168_);
                                lean_dec_ref_known(v_p_3159_, 2);
                                lean_del_object(v___x_3157_);
                                lean_dec(v_arg_3141_);
                                lean_dec_ref(v_P_3139_);
                                state = 1;
                                continue;
                            } else {
                                if lean_obj_tag(v_us_3176_) == 1 {
                                    v_tail_3189_ = lean_ctor_get(v_us_3176_, 1);
                                    lean_inc(v_tail_3189_);
                                    if lean_obj_tag(v_tail_3189_) == 1 {
                                        v_tail_3190_ = lean_ctor_get(v_tail_3189_, 1);
                                        if lean_obj_tag(v_tail_3190_) == 0 {
                                            v_head_3191_ = lean_ctor_get(v_tail_3189_, 0);
                                            v_isSharedCheck_3285_ =
                                                (!lean_is_exclusive(v_tail_3189_)) as u8;
                                            if v_isSharedCheck_3285_ == 0 {
                                                v_unused_3286_ = lean_ctor_get(v_tail_3189_, 1);
                                                lean_dec(v_unused_3286_);
                                                v___x_3193_ = v_tail_3189_;
                                                v_isShared_3194_ = v_isSharedCheck_3285_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_inc(v_head_3191_);
                                                lean_dec(v_tail_3189_);
                                                v___x_3193_ = lean_box(0);
                                                v_isShared_3194_ = v_isSharedCheck_3285_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref_known(v_tail_3189_, 2);
                                            lean_dec_ref(v_arg_3174_);
                                            lean_del_object(v___x_3171_);
                                            lean_dec(v_uniq_3169_);
                                            lean_dec(v_name_3168_);
                                            lean_dec_ref_known(v_p_3159_, 2);
                                            lean_del_object(v___x_3157_);
                                            lean_dec(v_arg_3141_);
                                            lean_dec_ref(v_P_3139_);
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_tail_3189_);
                                        lean_dec_ref(v_arg_3174_);
                                        lean_del_object(v___x_3171_);
                                        lean_dec(v_uniq_3169_);
                                        lean_dec(v_name_3168_);
                                        lean_dec_ref_known(v_p_3159_, 2);
                                        lean_del_object(v___x_3157_);
                                        lean_dec(v_arg_3141_);
                                        lean_dec_ref(v_P_3139_);
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_3174_);
                                    lean_del_object(v___x_3171_);
                                    lean_dec(v_uniq_3169_);
                                    lean_dec(v_name_3168_);
                                    lean_dec_ref_known(v_p_3159_, 2);
                                    lean_del_object(v___x_3157_);
                                    lean_dec(v_arg_3141_);
                                    lean_dec_ref(v_P_3139_);
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            4 => {
                lean_inc_ref(v_arg_3175_);
                if v_isShared_3158_ == 0 {
                    lean_ctor_set(v___x_3157_, 0, v_arg_3175_);
                    v___x_3196_ = v___x_3157_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_arg_3175_);
                    v___x_3196_ = v_reuseFailAlloc_3284_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3197_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__2;
                v___x_3198_ = lean_box(0);
                v___x_3199_ = l_Lean_Elab_Tactic_elabTermWithHoles(
                    v_arg_3141_,
                    v___x_3196_,
                    v___x_3197_,
                    v___x_3188_,
                    v___x_3198_,
                    v_a_3142_,
                    v_a_3143_,
                    v_a_3144_,
                    v_a_3145_,
                    v_a_3146_,
                    v_a_3147_,
                    v_a_3148_,
                    v_a_3149_,
                );
                if lean_obj_tag(v___x_3199_) == 0 {
                    v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
                    lean_inc(v_a_3200_);
                    lean_dec_ref_known(v___x_3199_, 1);
                    v_fst_3201_ = lean_ctor_get(v_a_3200_, 0);
                    v_snd_3202_ = lean_ctor_get(v_a_3200_, 1);
                    v_isSharedCheck_3268_ = (!lean_is_exclusive(v_a_3200_)) as u8;
                    if v_isSharedCheck_3268_ == 0 {
                        v___x_3204_ = v_a_3200_;
                        v_isShared_3205_ = v_isSharedCheck_3268_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_3202_);
                        lean_inc(v_fst_3201_);
                        lean_dec(v_a_3200_);
                        v___x_3204_ = lean_box(0);
                        v_isShared_3205_ = v_isSharedCheck_3268_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3193_);
                    lean_dec(v_head_3191_);
                    lean_dec_ref(v_arg_3174_);
                    lean_del_object(v___x_3171_);
                    lean_dec(v_uniq_3169_);
                    lean_dec(v_name_3168_);
                    lean_dec_ref_known(v_p_3159_, 2);
                    lean_dec_ref(v_P_3139_);
                    v_a_3269_ = lean_ctor_get(v___x_3199_, 0);
                    v_isSharedCheck_3283_ = (!lean_is_exclusive(v___x_3199_)) as u8;
                    if v_isSharedCheck_3283_ == 0 {
                        v___x_3271_ = v___x_3199_;
                        v_isShared_3272_ = v_isSharedCheck_3283_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3269_);
                        lean_dec(v___x_3199_);
                        v___x_3271_ = lean_box(0);
                        v_isShared_3272_ = v_isSharedCheck_3283_;
                        state = 17;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3206_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_3202_, v_a_3143_);
                if lean_obj_tag(v___x_3206_) == 0 {
                    v_isSharedCheck_3258_ = (!lean_is_exclusive(v___x_3206_)) as u8;
                    if v_isSharedCheck_3258_ == 0 {
                        v_unused_3259_ = lean_ctor_get(v___x_3206_, 0);
                        lean_dec(v_unused_3259_);
                        v___x_3208_ = v___x_3206_;
                        v_isShared_3209_ = v_isSharedCheck_3258_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_3206_);
                        v___x_3208_ = lean_box(0);
                        v_isShared_3209_ = v_isSharedCheck_3258_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3204_);
                    lean_dec(v_fst_3201_);
                    lean_del_object(v___x_3193_);
                    lean_dec(v_head_3191_);
                    lean_dec_ref(v_arg_3174_);
                    lean_del_object(v___x_3171_);
                    lean_dec(v_uniq_3169_);
                    lean_dec(v_name_3168_);
                    lean_dec_ref_known(v_p_3159_, 2);
                    lean_dec_ref(v_P_3139_);
                    v_a_3260_ = lean_ctor_get(v___x_3206_, 0);
                    v_isSharedCheck_3267_ = (!lean_is_exclusive(v___x_3206_)) as u8;
                    if v_isSharedCheck_3267_ == 0 {
                        v___x_3262_ = v___x_3206_;
                        v_isShared_3263_ = v_isSharedCheck_3267_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3260_);
                        lean_dec(v___x_3206_);
                        v___x_3262_ = lean_box(0);
                        v_isShared_3263_ = v_isSharedCheck_3267_;
                        state = 15;
                        continue;
                    }
                }
            }
            7 => {
                v_options_3210_ = lean_ctor_get(v_a_3148_, 2);
                v_inheritedTraceOptions_3211_ = lean_ctor_get(v_a_3148_, 13);
                v_hasTrace_3212_ = lean_ctor_get_uint8(
                    v_options_3210_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_3213_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__1;
                lean_inc_ref(v_us_3176_);
                v___x_3214_ = l_Lean_mkConst(v___x_3213_, v_us_3176_);
                lean_inc_n(v_fst_3201_, 2);
                lean_inc_ref(v_P_3139_);
                lean_inc_ref_n(v_arg_3173_, 2);
                lean_inc_ref(v_arg_3174_);
                lean_inc_ref(v_arg_3175_);
                v___x_3215_ = l_Lean_mkApp5(
                    v___x_3214_,
                    v_arg_3175_,
                    v_arg_3174_,
                    v_arg_3173_,
                    v_P_3139_,
                    v_fst_3201_,
                );
                v___x_3216_ = lean_unsigned_to_nat(1);
                v___x_3217_ = lean_mk_empty_array_with_capacity(v___x_3216_);
                v___x_3218_ = lean_array_push(v___x_3217_, v_fst_3201_);
                v___x_3219_ = l_Lean_Expr_beta(v_arg_3173_, v___x_3218_);
                if v_hasTrace_3212_ == 0 {
                    lean_dec(v_fst_3201_);
                    lean_del_object(v___x_3193_);
                    lean_dec(v_head_3191_);
                    lean_dec_ref(v_arg_3174_);
                    lean_dec_ref_known(v_p_3159_, 2);
                    lean_dec_ref(v_P_3139_);
                    state = 8;
                    continue;
                } else {
                    v___x_3232_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                    v___x_3233_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__11);
                    v___x_3234_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3211_,
                        v_options_3210_,
                        v___x_3233_,
                    );
                    if v___x_3234_ == 0 {
                        lean_dec(v_fst_3201_);
                        lean_del_object(v___x_3193_);
                        lean_dec(v_head_3191_);
                        lean_dec_ref(v_arg_3174_);
                        lean_dec_ref_known(v_p_3159_, 2);
                        lean_dec_ref(v_P_3139_);
                        state = 8;
                        continue;
                    } else {
                        v___x_3235_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___closed__3,
                        );
                        v___x_3236_ = l_Lean_MessageData_ofExpr(v_p_3159_);
                        if v_isShared_3194_ == 0 {
                            lean_ctor_set_tag(v___x_3193_, 7);
                            lean_ctor_set(v___x_3193_, 1, v___x_3236_);
                            lean_ctor_set(v___x_3193_, 0, v___x_3235_);
                            v___x_3238_ = v___x_3193_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_3257_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3235_);
                            lean_ctor_set(v_reuseFailAlloc_3257_, 1, v___x_3236_);
                            v___x_3238_ = v_reuseFailAlloc_3257_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v_isShared_3172_ == 0 {
                    lean_ctor_set(v___x_3171_, 2, v___x_3219_);
                    v___x_3222_ = v___x_3171_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_name_3168_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_uniq_3169_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 2, v___x_3219_);
                    v___x_3222_ = v_reuseFailAlloc_3231_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3223_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_3222_);
                if v_isShared_3205_ == 0 {
                    lean_ctor_set(v___x_3204_, 1, v___x_3215_);
                    lean_ctor_set(v___x_3204_, 0, v___x_3223_);
                    v___x_3225_ = v___x_3204_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3223_);
                    lean_ctor_set(v_reuseFailAlloc_3230_, 1, v___x_3215_);
                    v___x_3225_ = v_reuseFailAlloc_3230_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3226_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3226_, 0, v___x_3225_);
                if v_isShared_3209_ == 0 {
                    lean_ctor_set(v___x_3208_, 0, v___x_3226_);
                    v___x_3228_ = v___x_3208_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3226_);
                    v___x_3228_ = v_reuseFailAlloc_3229_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3228_;
            }
            12 => {
                v___x_3239_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8,
                );
                v___x_3240_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3240_, 0, v___x_3238_);
                lean_ctor_set(v___x_3240_, 1, v___x_3239_);
                v___x_3241_ = l_Lean_MessageData_ofExpr(v_fst_3201_);
                v___x_3242_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3242_, 0, v___x_3240_);
                lean_ctor_set(v___x_3242_, 1, v___x_3241_);
                v___x_3243_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__15,
                );
                v___x_3244_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3244_, 0, v___x_3242_);
                lean_ctor_set(v___x_3244_, 1, v___x_3243_);
                lean_inc_ref(v___x_3219_);
                v___x_3245_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_head_3191_,
                    v_arg_3174_,
                    v_P_3139_,
                    v___x_3219_,
                );
                v___x_3246_ = l_Lean_MessageData_ofExpr(v___x_3245_);
                v___x_3247_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3247_, 0, v___x_3244_);
                lean_ctor_set(v___x_3247_, 1, v___x_3246_);
                v___x_3248_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__1___redArg(v___x_3232_, v___x_3247_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_);
                if lean_obj_tag(v___x_3248_) == 0 {
                    lean_dec_ref_known(v___x_3248_, 1);
                    state = 8;
                    continue;
                } else {
                    lean_dec_ref(v___x_3219_);
                    lean_dec_ref(v___x_3215_);
                    lean_del_object(v___x_3208_);
                    lean_del_object(v___x_3204_);
                    lean_del_object(v___x_3171_);
                    lean_dec(v_uniq_3169_);
                    lean_dec(v_name_3168_);
                    v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
                    v_isSharedCheck_3256_ = (!lean_is_exclusive(v___x_3248_)) as u8;
                    if v_isSharedCheck_3256_ == 0 {
                        v___x_3251_ = v___x_3248_;
                        v_isShared_3252_ = v_isSharedCheck_3256_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3249_);
                        lean_dec(v___x_3248_);
                        v___x_3251_ = lean_box(0);
                        v_isShared_3252_ = v_isSharedCheck_3256_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_3252_ == 0 {
                    v___x_3254_ = v___x_3251_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
                    v___x_3254_ = v_reuseFailAlloc_3255_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3254_;
            }
            15 => {
                if v_isShared_3263_ == 0 {
                    v___x_3265_ = v___x_3262_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
                    v___x_3265_ = v_reuseFailAlloc_3266_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3265_;
            }
            17 => {
                v___x_3281_ = l_Lean_Exception_isInterrupt(v_a_3269_);
                if v___x_3281_ == 0 {
                    lean_inc(v_a_3269_);
                    v___x_3282_ = l_Lean_Exception_isRuntime(v_a_3269_);
                    v___y_3274_ = v___x_3282_;
                    state = 18;
                    continue;
                } else {
                    v___y_3274_ = v___x_3281_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_3274_ == 0 {
                    lean_dec(v_a_3269_);
                    if v_isShared_3272_ == 0 {
                        lean_ctor_set_tag(v___x_3271_, 0);
                        lean_ctor_set(v___x_3271_, 0, v___x_3198_);
                        v___x_3276_ = v___x_3271_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3198_);
                        v___x_3276_ = v_reuseFailAlloc_3277_;
                        state = 19;
                        continue;
                    }
                } else {
                    if v_isShared_3272_ == 0 {
                        v___x_3279_ = v___x_3271_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3269_);
                        v___x_3279_ = v_reuseFailAlloc_3280_;
                        state = 20;
                        continue;
                    }
                }
            }
            19 => {
                return v___x_3276_;
            }
            20 => {
                return v___x_3279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall___boxed(
    mut v_P_3292_: *mut LeanObject,
    mut v_00_u03a8_3293_: *mut LeanObject,
    mut v_arg_3294_: *mut LeanObject,
    mut v_a_3295_: *mut LeanObject,
    mut v_a_3296_: *mut LeanObject,
    mut v_a_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
    mut v_a_3299_: *mut LeanObject,
    mut v_a_3300_: *mut LeanObject,
    mut v_a_3301_: *mut LeanObject,
    mut v_a_3302_: *mut LeanObject,
    mut v_a_3303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3304_: *mut LeanObject = core::ptr::null_mut();
    v_res_3304_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(
        v_P_3292_,
        v_00_u03a8_3293_,
        v_arg_3294_,
        v_a_3295_,
        v_a_3296_,
        v_a_3297_,
        v_a_3298_,
        v_a_3299_,
        v_a_3300_,
        v_a_3301_,
        v_a_3302_,
    );
    lean_dec(v_a_3302_);
    lean_dec_ref(v_a_3301_);
    lean_dec(v_a_3300_);
    lean_dec_ref(v_a_3299_);
    lean_dec(v_a_3298_);
    lean_dec_ref(v_a_3297_);
    lean_dec(v_a_3296_);
    lean_dec_ref(v_a_3295_);
    return v_res_3304_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    v___x_3305_ = lean_box(0);
    v___x_3306_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3307_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3307_, 0, v___x_3306_);
    lean_ctor_set(v___x_3307_, 1, v___x_3305_);
    return v___x_3307_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    v___x_3309_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___closed__0);
    v___x_3310_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3310_, 0, v___x_3309_);
    return v___x_3310_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg___boxed(
    mut v___y_3311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3312_: *mut LeanObject = core::ptr::null_mut();
    v_res_3312_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
    return v_res_3312_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(
    mut v_00_u03b1_3313_: *mut LeanObject,
    mut v___y_3314_: *mut LeanObject,
    mut v___y_3315_: *mut LeanObject,
    mut v___y_3316_: *mut LeanObject,
    mut v___y_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    v___x_3323_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
    return v___x_3323_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___boxed(
    mut v_00_u03b1_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
    mut v___y_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3334_: *mut LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0(v_00_u03b1_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
    lean_dec(v___y_3332_);
    lean_dec_ref(v___y_3331_);
    lean_dec(v___y_3330_);
    lean_dec_ref(v___y_3329_);
    lean_dec(v___y_3328_);
    lean_dec_ref(v___y_3327_);
    lean_dec(v___y_3326_);
    lean_dec_ref(v___y_3325_);
    return v_res_3334_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(
    mut v_msg_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
    mut v___y_3342_: *mut LeanObject,
    mut v___y_3343_: *mut LeanObject,
    mut v___y_3344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235__overap_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    v___f_3346_ =
        l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___closed__0;
    v___x_6235__overap_3347_ = lean_panic_fn_borrowed(v___f_3346_, v_msg_3336_);
    lean_inc(v___y_3344_);
    lean_inc_ref(v___y_3343_);
    lean_inc(v___y_3342_);
    lean_inc_ref(v___y_3341_);
    lean_inc(v___y_3340_);
    lean_inc_ref(v___y_3339_);
    lean_inc(v___y_3338_);
    lean_inc_ref(v___y_3337_);
    v___x_3348_ = lean_apply_9(
        v___x_6235__overap_3347_,
        v___y_3337_,
        v___y_3338_,
        v___y_3339_,
        v___y_3340_,
        v___y_3341_,
        v___y_3342_,
        v___y_3343_,
        v___y_3344_,
        lean_box(0),
    );
    return v___x_3348_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3___boxed(
    mut v_msg_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3359_: *mut LeanObject = core::ptr::null_mut();
    v_res_3359_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(
        v_msg_3349_,
        v___y_3350_,
        v___y_3351_,
        v___y_3352_,
        v___y_3353_,
        v___y_3354_,
        v___y_3355_,
        v___y_3356_,
        v___y_3357_,
    );
    lean_dec(v___y_3357_);
    lean_dec_ref(v___y_3356_);
    lean_dec(v___y_3355_);
    lean_dec_ref(v___y_3354_);
    lean_dec(v___y_3353_);
    lean_dec_ref(v___y_3352_);
    lean_dec(v___y_3351_);
    lean_dec_ref(v___y_3350_);
    return v_res_3359_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(
    mut v_x_3360_: *mut LeanObject,
    mut v___y_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
    mut v___y_3368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3364_);
    lean_inc_ref(v___y_3363_);
    lean_inc(v___y_3362_);
    lean_inc_ref(v___y_3361_);
    v___x_3370_ = lean_apply_9(
        v_x_3360_,
        v___y_3361_,
        v___y_3362_,
        v___y_3363_,
        v___y_3364_,
        v___y_3365_,
        v___y_3366_,
        v___y_3367_,
        v___y_3368_,
        lean_box(0),
    );
    return v___x_3370_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed(
    mut v_x_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
    mut v___y_3373_: *mut LeanObject,
    mut v___y_3374_: *mut LeanObject,
    mut v___y_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
    mut v___y_3379_: *mut LeanObject,
    mut v___y_3380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3381_: *mut LeanObject = core::ptr::null_mut();
    v_res_3381_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0(v_x_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
    lean_dec(v___y_3375_);
    lean_dec_ref(v___y_3374_);
    lean_dec(v___y_3373_);
    lean_dec_ref(v___y_3372_);
    return v_res_3381_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(
    mut v_mvarId_3382_: *mut LeanObject,
    mut v_x_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3398_: u8 = 0;
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3387_);
                lean_inc_ref(v___y_3386_);
                lean_inc(v___y_3385_);
                lean_inc_ref(v___y_3384_);
                v___f_3393_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_3393_, 0, v_x_3383_);
                lean_closure_set(v___f_3393_, 1, v___y_3384_);
                lean_closure_set(v___f_3393_, 2, v___y_3385_);
                lean_closure_set(v___f_3393_, 3, v___y_3386_);
                lean_closure_set(v___f_3393_, 4, v___y_3387_);
                v___x_3394_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_3382_,
                    v___f_3393_,
                    v___y_3388_,
                    v___y_3389_,
                    v___y_3390_,
                    v___y_3391_,
                );
                if lean_obj_tag(v___x_3394_) == 0 {
                    return v___x_3394_;
                } else {
                    v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
                    v_isSharedCheck_3402_ = (!lean_is_exclusive(v___x_3394_)) as u8;
                    if v_isSharedCheck_3402_ == 0 {
                        v___x_3397_ = v___x_3394_;
                        v_isShared_3398_ = v_isSharedCheck_3402_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3395_);
                        lean_dec(v___x_3394_);
                        v___x_3397_ = lean_box(0);
                        v_isShared_3398_ = v_isSharedCheck_3402_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3398_ == 0 {
                    v___x_3400_ = v___x_3397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
                    v___x_3400_ = v_reuseFailAlloc_3401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg___boxed(
    mut v_mvarId_3403_: *mut LeanObject,
    mut v_x_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
    mut v___y_3407_: *mut LeanObject,
    mut v___y_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
    mut v___y_3411_: *mut LeanObject,
    mut v___y_3412_: *mut LeanObject,
    mut v___y_3413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3414_: *mut LeanObject = core::ptr::null_mut();
    v_res_3414_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_3403_, v_x_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
    lean_dec(v___y_3412_);
    lean_dec_ref(v___y_3411_);
    lean_dec(v___y_3410_);
    lean_dec_ref(v___y_3409_);
    lean_dec(v___y_3408_);
    lean_dec_ref(v___y_3407_);
    lean_dec(v___y_3406_);
    lean_dec_ref(v___y_3405_);
    return v_res_3414_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(
    mut v_00_u03b1_3415_: *mut LeanObject,
    mut v_mvarId_3416_: *mut LeanObject,
    mut v_x_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
    mut v___y_3422_: *mut LeanObject,
    mut v___y_3423_: *mut LeanObject,
    mut v___y_3424_: *mut LeanObject,
    mut v___y_3425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    v___x_3427_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_mvarId_3416_, v_x_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
    return v___x_3427_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___boxed(
    mut v_00_u03b1_3428_: *mut LeanObject,
    mut v_mvarId_3429_: *mut LeanObject,
    mut v_x_3430_: *mut LeanObject,
    mut v___y_3431_: *mut LeanObject,
    mut v___y_3432_: *mut LeanObject,
    mut v___y_3433_: *mut LeanObject,
    mut v___y_3434_: *mut LeanObject,
    mut v___y_3435_: *mut LeanObject,
    mut v___y_3436_: *mut LeanObject,
    mut v___y_3437_: *mut LeanObject,
    mut v___y_3438_: *mut LeanObject,
    mut v___y_3439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3440_: *mut LeanObject = core::ptr::null_mut();
    v_res_3440_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4(
            v_00_u03b1_3428_,
            v_mvarId_3429_,
            v_x_3430_,
            v___y_3431_,
            v___y_3432_,
            v___y_3433_,
            v___y_3434_,
            v___y_3435_,
            v___y_3436_,
            v___y_3437_,
            v___y_3438_,
        );
    lean_dec(v___y_3438_);
    lean_dec_ref(v___y_3437_);
    lean_dec(v___y_3436_);
    lean_dec_ref(v___y_3435_);
    lean_dec(v___y_3434_);
    lean_dec_ref(v___y_3433_);
    lean_dec(v___y_3432_);
    lean_dec_ref(v___y_3431_);
    return v_res_3440_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0(
    mut v___x_3443_: *mut LeanObject,
    mut v___x_3444_: *mut LeanObject,
    mut v___x_3445_: *mut LeanObject,
    mut v___x_3446_: *mut LeanObject,
    mut v___x_3447_: *mut LeanObject,
    mut v___x_3448_: *mut LeanObject,
    mut v___x_3449_: *mut LeanObject,
    mut v_fst_3450_: *mut LeanObject,
    mut v_fst_3451_: *mut LeanObject,
    mut v___x_3452_: *mut LeanObject,
    mut v_snd_3453_: *mut LeanObject,
    mut v_snd_3454_: *mut LeanObject,
    mut v_hgoal_3455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__0;
    v___x_3457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0___closed__1;
    v___x_3458_ = l_Lean_Name_mkStr5(
        v___x_3443_,
        v___x_3444_,
        v___x_3445_,
        v___x_3456_,
        v___x_3457_,
    );
    v___x_3459_ = l_Lean_mkConst(v___x_3458_, v___x_3446_);
    lean_inc_ref(v___x_3449_);
    lean_inc_ref_n(v___x_3448_, 2);
    lean_inc(v___x_3447_);
    v___x_3460_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
        v___x_3447_,
        v___x_3448_,
        v___x_3449_,
        v_fst_3450_,
    );
    v___x_3461_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
        v___x_3447_,
        v___x_3448_,
        v___x_3449_,
        v_fst_3451_,
    );
    v___x_3462_ = l_Lean_mkApp6(
        v___x_3459_,
        v___x_3448_,
        v___x_3460_,
        v___x_3461_,
        v___x_3452_,
        v_snd_3453_,
        v_hgoal_3455_,
    );
    v___x_3463_ = lean_apply_1(v_snd_3454_, v___x_3462_);
    return v___x_3463_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    v___x_3465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__0;
    v___x_3466_ = l_Lean_stringToMessageData(v___x_3465_);
    return v___x_3466_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(
    mut v___x_3467_: *mut LeanObject,
    mut v___x_3468_: *mut LeanObject,
    mut v___x_3469_: *mut LeanObject,
    mut v___x_3470_: *mut LeanObject,
    mut v___x_3471_: *mut LeanObject,
    mut v_as_3472_: *mut LeanObject,
    mut v_sz_3473_: usize,
    mut v_i_3474_: usize,
    mut v_b_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: usize = 0;
    let mut v___x_3488_: usize = 0;
    let mut v___x_3490_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3496_: u8 = 0;
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3518_: u8 = 0;
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_val_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___f_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut v_a_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3537_: u8 = 0;
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3541_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3490_ = lean_usize_dec_lt(v_i_3474_, v_sz_3473_);
                if v___x_3490_ == 0 {
                    lean_dec_ref(v___x_3471_);
                    lean_dec_ref(v___x_3470_);
                    lean_dec_ref(v___x_3469_);
                    lean_dec(v___x_3468_);
                    lean_dec(v___x_3467_);
                    v___x_3491_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3491_, 0, v_b_3475_);
                    return v___x_3491_;
                } else {
                    v_fst_3492_ = lean_ctor_get(v_b_3475_, 0);
                    v_snd_3493_ = lean_ctor_get(v_b_3475_, 1);
                    v_isSharedCheck_3547_ = (!lean_is_exclusive(v_b_3475_)) as u8;
                    if v_isSharedCheck_3547_ == 0 {
                        v___x_3495_ = v_b_3475_;
                        v_isShared_3496_ = v_isSharedCheck_3547_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3493_);
                        lean_inc(v_fst_3492_);
                        lean_dec(v_b_3475_);
                        v___x_3495_ = lean_box(0);
                        v_isShared_3496_ = v_isSharedCheck_3547_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3487_ = 1usize;
                v___x_3488_ = lean_usize_add(v_i_3474_, v___x_3487_);
                v_i_3474_ = v___x_3488_;
                v_b_3475_ = v_a_3486_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3497_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0;
                v___x_3498_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                v___x_3499_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1;
                v_a_3500_ = lean_array_uget_borrowed(v_as_3472_, v_i_3474_);
                lean_inc(v_a_3500_);
                lean_inc(v_fst_3492_);
                lean_inc_ref(v___x_3470_);
                v___x_3542_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(
                    v___x_3470_,
                    v_fst_3492_,
                    v_a_3500_,
                    v___y_3476_,
                    v___y_3477_,
                    v___y_3478_,
                    v___y_3479_,
                    v___y_3480_,
                    v___y_3481_,
                    v___y_3482_,
                    v___y_3483_,
                );
                if lean_obj_tag(v___x_3542_) == 0 {
                    v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
                    lean_inc(v_a_3543_);
                    if lean_obj_tag(v_a_3543_) == 0 {
                        lean_dec_ref_known(v___x_3542_, 1);
                        lean_inc(v_a_3500_);
                        lean_inc(v_fst_3492_);
                        lean_inc_ref(v___x_3470_);
                        v___x_3544_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(
                            v___x_3470_,
                            v_fst_3492_,
                            v_a_3500_,
                            v___y_3476_,
                            v___y_3477_,
                            v___y_3478_,
                            v___y_3479_,
                            v___y_3480_,
                            v___y_3481_,
                            v___y_3482_,
                            v___y_3483_,
                        );
                        if lean_obj_tag(v___x_3544_) == 0 {
                            v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
                            lean_inc(v_a_3545_);
                            if lean_obj_tag(v_a_3545_) == 0 {
                                lean_dec_ref_known(v___x_3544_, 1);
                                lean_inc(v_a_3500_);
                                lean_inc(v_fst_3492_);
                                lean_inc_ref(v___x_3470_);
                                v___x_3546_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(
                                    v___x_3470_,
                                    v_fst_3492_,
                                    v_a_3500_,
                                    v___y_3476_,
                                    v___y_3477_,
                                    v___y_3478_,
                                    v___y_3479_,
                                    v___y_3480_,
                                    v___y_3481_,
                                    v___y_3482_,
                                    v___y_3483_,
                                );
                                v___y_3502_ = v___x_3546_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec_ref_known(v_a_3545_, 1);
                                v___y_3502_ = v___x_3544_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___y_3502_ = v___x_3544_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_3543_, 1);
                        v___y_3502_ = v___x_3542_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_3502_ = v___x_3542_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v___y_3502_) == 0 {
                    v_a_3503_ = lean_ctor_get(v___y_3502_, 0);
                    lean_inc(v_a_3503_);
                    lean_dec_ref_known(v___y_3502_, 1);
                    if lean_obj_tag(v_a_3503_) == 0 {
                        v___x_3504_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
                        lean_inc(v_fst_3492_);
                        v___x_3505_ = l_Lean_MessageData_ofExpr(v_fst_3492_);
                        v___x_3506_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3506_, 0, v___x_3504_);
                        lean_ctor_set(v___x_3506_, 1, v___x_3505_);
                        v___x_3507_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
                        v___x_3508_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3508_, 0, v___x_3506_);
                        lean_ctor_set(v___x_3508_, 1, v___x_3507_);
                        lean_inc(v_a_3500_);
                        v___x_3509_ = l_Lean_MessageData_ofSyntax(v_a_3500_);
                        v___x_3510_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3510_, 0, v___x_3508_);
                        lean_ctor_set(v___x_3510_, 1, v___x_3509_);
                        v___x_3511_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_3510_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
                        if lean_obj_tag(v___x_3511_) == 0 {
                            lean_dec_ref_known(v___x_3511_, 1);
                            if v_isShared_3496_ == 0 {
                                v___x_3513_ = v___x_3495_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_fst_3492_);
                                lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_snd_3493_);
                                v___x_3513_ = v_reuseFailAlloc_3514_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3495_);
                            lean_dec(v_snd_3493_);
                            lean_dec(v_fst_3492_);
                            lean_dec_ref(v___x_3471_);
                            lean_dec_ref(v___x_3470_);
                            lean_dec_ref(v___x_3469_);
                            lean_dec(v___x_3468_);
                            lean_dec(v___x_3467_);
                            v_a_3515_ = lean_ctor_get(v___x_3511_, 0);
                            v_isSharedCheck_3522_ = (!lean_is_exclusive(v___x_3511_)) as u8;
                            if v_isSharedCheck_3522_ == 0 {
                                v___x_3517_ = v___x_3511_;
                                v_isShared_3518_ = v_isSharedCheck_3522_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3515_);
                                lean_dec(v___x_3511_);
                                v___x_3517_ = lean_box(0);
                                v_isShared_3518_ = v_isSharedCheck_3522_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_3495_);
                        v_val_3523_ = lean_ctor_get(v_a_3503_, 0);
                        lean_inc(v_val_3523_);
                        lean_dec_ref_known(v_a_3503_, 1);
                        v_fst_3524_ = lean_ctor_get(v_val_3523_, 0);
                        v_snd_3525_ = lean_ctor_get(v_val_3523_, 1);
                        v_isSharedCheck_3533_ = (!lean_is_exclusive(v_val_3523_)) as u8;
                        if v_isSharedCheck_3533_ == 0 {
                            v___x_3527_ = v_val_3523_;
                            v_isShared_3528_ = v_isSharedCheck_3533_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_snd_3525_);
                            lean_inc(v_fst_3524_);
                            lean_dec(v_val_3523_);
                            v___x_3527_ = lean_box(0);
                            v_isShared_3528_ = v_isSharedCheck_3533_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3495_);
                    lean_dec(v_snd_3493_);
                    lean_dec(v_fst_3492_);
                    lean_dec_ref(v___x_3471_);
                    lean_dec_ref(v___x_3470_);
                    lean_dec_ref(v___x_3469_);
                    lean_dec(v___x_3468_);
                    lean_dec(v___x_3467_);
                    v_a_3534_ = lean_ctor_get(v___y_3502_, 0);
                    v_isSharedCheck_3541_ = (!lean_is_exclusive(v___y_3502_)) as u8;
                    if v_isSharedCheck_3541_ == 0 {
                        v___x_3536_ = v___y_3502_;
                        v_isShared_3537_ = v_isSharedCheck_3541_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3534_);
                        lean_dec(v___y_3502_);
                        v___x_3536_ = lean_box(0);
                        v_isShared_3537_ = v_isSharedCheck_3541_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v_a_3486_ = v___x_3513_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_3518_ == 0 {
                    v___x_3520_ = v___x_3517_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
                    v___x_3520_ = v_reuseFailAlloc_3521_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3520_;
            }
            7 => {
                lean_inc_ref(v___x_3471_);
                lean_inc(v_fst_3524_);
                lean_inc_ref(v___x_3470_);
                lean_inc_ref(v___x_3469_);
                lean_inc(v___x_3468_);
                lean_inc(v___x_3467_);
                v___f_3529_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0 as *mut core::ffi::c_void, 13, 12);
                lean_closure_set(v___f_3529_, 0, v___x_3497_);
                lean_closure_set(v___f_3529_, 1, v___x_3498_);
                lean_closure_set(v___f_3529_, 2, v___x_3499_);
                lean_closure_set(v___f_3529_, 3, v___x_3467_);
                lean_closure_set(v___f_3529_, 4, v___x_3468_);
                lean_closure_set(v___f_3529_, 5, v___x_3469_);
                lean_closure_set(v___f_3529_, 6, v___x_3470_);
                lean_closure_set(v___f_3529_, 7, v_fst_3492_);
                lean_closure_set(v___f_3529_, 8, v_fst_3524_);
                lean_closure_set(v___f_3529_, 9, v___x_3471_);
                lean_closure_set(v___f_3529_, 10, v_snd_3525_);
                lean_closure_set(v___f_3529_, 11, v_snd_3493_);
                if v_isShared_3528_ == 0 {
                    lean_ctor_set(v___x_3527_, 1, v___f_3529_);
                    v___x_3531_ = v___x_3527_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_fst_3524_);
                    lean_ctor_set(v_reuseFailAlloc_3532_, 1, v___f_3529_);
                    v___x_3531_ = v_reuseFailAlloc_3532_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_3486_ = v___x_3531_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_3537_ == 0 {
                    v___x_3539_ = v___x_3536_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
                    v___x_3539_ = v_reuseFailAlloc_3540_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3548_: *mut LeanObject = *_args.add(0);
    let mut v___x_3549_: *mut LeanObject = *_args.add(1);
    let mut v___x_3550_: *mut LeanObject = *_args.add(2);
    let mut v___x_3551_: *mut LeanObject = *_args.add(3);
    let mut v___x_3552_: *mut LeanObject = *_args.add(4);
    let mut v_as_3553_: *mut LeanObject = *_args.add(5);
    let mut v_sz_3554_: *mut LeanObject = *_args.add(6);
    let mut v_i_3555_: *mut LeanObject = *_args.add(7);
    let mut v_b_3556_: *mut LeanObject = *_args.add(8);
    let mut v___y_3557_: *mut LeanObject = *_args.add(9);
    let mut v___y_3558_: *mut LeanObject = *_args.add(10);
    let mut v___y_3559_: *mut LeanObject = *_args.add(11);
    let mut v___y_3560_: *mut LeanObject = *_args.add(12);
    let mut v___y_3561_: *mut LeanObject = *_args.add(13);
    let mut v___y_3562_: *mut LeanObject = *_args.add(14);
    let mut v___y_3563_: *mut LeanObject = *_args.add(15);
    let mut v___y_3564_: *mut LeanObject = *_args.add(16);
    let mut v___y_3565_: *mut LeanObject = *_args.add(17);
    let mut v_sz_boxed_3566_: usize = 0;
    let mut v_i_boxed_3567_: usize = 0;
    let mut v_res_3568_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3566_ = lean_unbox_usize(v_sz_3554_);
    lean_dec(v_sz_3554_);
    v_i_boxed_3567_ = lean_unbox_usize(v_i_3555_);
    lean_dec(v_i_3555_);
    v_res_3568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_3548_, v___x_3549_, v___x_3550_, v___x_3551_, v___x_3552_, v_as_3553_, v_sz_boxed_3566_, v_i_boxed_3567_, v_b_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
    lean_dec(v___y_3564_);
    lean_dec_ref(v___y_3563_);
    lean_dec(v___y_3562_);
    lean_dec_ref(v___y_3561_);
    lean_dec(v___y_3560_);
    lean_dec_ref(v___y_3559_);
    lean_dec(v___y_3558_);
    lean_dec_ref(v___y_3557_);
    lean_dec_ref(v_as_3553_);
    return v_res_3568_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(
    mut v_x_3569_: *mut LeanObject,
    mut v_x_3570_: *mut LeanObject,
    mut v_x_3571_: *mut LeanObject,
    mut v_x_3572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3577_: u8 = 0;
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: u8 = 0;
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3598_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3573_ = lean_ctor_get(v_x_3569_, 0);
                v_vs_3574_ = lean_ctor_get(v_x_3569_, 1);
                v_isSharedCheck_3598_ = (!lean_is_exclusive(v_x_3569_)) as u8;
                if v_isSharedCheck_3598_ == 0 {
                    v___x_3576_ = v_x_3569_;
                    v_isShared_3577_ = v_isSharedCheck_3598_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3574_);
                    lean_inc(v_ks_3573_);
                    lean_dec(v_x_3569_);
                    v___x_3576_ = lean_box(0);
                    v_isShared_3577_ = v_isSharedCheck_3598_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3578_ = lean_array_get_size(v_ks_3573_);
                v___x_3579_ = lean_nat_dec_lt(v_x_3570_, v___x_3578_);
                if v___x_3579_ == 0 {
                    lean_dec(v_x_3570_);
                    v___x_3580_ = lean_array_push(v_ks_3573_, v_x_3571_);
                    v___x_3581_ = lean_array_push(v_vs_3574_, v_x_3572_);
                    if v_isShared_3577_ == 0 {
                        lean_ctor_set(v___x_3576_, 1, v___x_3581_);
                        lean_ctor_set(v___x_3576_, 0, v___x_3580_);
                        v___x_3583_ = v___x_3576_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3580_);
                        lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3581_);
                        v___x_3583_ = v_reuseFailAlloc_3584_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3585_ = lean_array_fget_borrowed(v_ks_3573_, v_x_3570_);
                    v___x_3586_ = l_Lean_instBEqMVarId_beq(v_x_3571_, v_k_x27_3585_);
                    if v___x_3586_ == 0 {
                        if v_isShared_3577_ == 0 {
                            v___x_3588_ = v___x_3576_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_ks_3573_);
                            lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_vs_3574_);
                            v___x_3588_ = v_reuseFailAlloc_3592_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3593_ = lean_array_fset(v_ks_3573_, v_x_3570_, v_x_3571_);
                        v___x_3594_ = lean_array_fset(v_vs_3574_, v_x_3570_, v_x_3572_);
                        lean_dec(v_x_3570_);
                        if v_isShared_3577_ == 0 {
                            lean_ctor_set(v___x_3576_, 1, v___x_3594_);
                            lean_ctor_set(v___x_3576_, 0, v___x_3593_);
                            v___x_3596_ = v___x_3576_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3593_);
                            lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___x_3594_);
                            v___x_3596_ = v_reuseFailAlloc_3597_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3583_;
            }
            3 => {
                v___x_3589_ = lean_unsigned_to_nat(1);
                v___x_3590_ = lean_nat_add(v_x_3570_, v___x_3589_);
                lean_dec(v_x_3570_);
                v_x_3569_ = v___x_3588_;
                v_x_3570_ = v___x_3590_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(
    mut v_n_3599_: *mut LeanObject,
    mut v_k_3600_: *mut LeanObject,
    mut v_v_3601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    v___x_3602_ = lean_unsigned_to_nat(0);
    v___x_3603_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_n_3599_, v___x_3602_, v_k_3600_, v_v_3601_);
    return v___x_3603_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0()
-> usize {
    let mut v___x_3604_: usize = 0;
    let mut v___x_3605_: usize = 0;
    let mut v___x_3606_: usize = 0;
    v___x_3604_ = 5usize;
    v___x_3605_ = 1usize;
    v___x_3606_ = lean_usize_shift_left(v___x_3605_, v___x_3604_);
    return v___x_3606_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1()
-> usize {
    let mut v___x_3607_: usize = 0;
    let mut v___x_3608_: usize = 0;
    let mut v___x_3609_: usize = 0;
    v___x_3607_ = 1usize;
    v___x_3608_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__0);
    v___x_3609_ = lean_usize_sub(v___x_3608_, v___x_3607_);
    return v___x_3609_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    v___x_3610_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3610_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(
    mut v_x_3611_: *mut LeanObject,
    mut v_x_3612_: usize,
    mut v_x_3613_: usize,
    mut v_x_3614_: *mut LeanObject,
    mut v_x_3615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: usize = 0;
    let mut v___x_3618_: usize = 0;
    let mut v___x_3619_: usize = 0;
    let mut v___x_3620_: usize = 0;
    let mut v_j_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3626_: u8 = 0;
    let mut v_v_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3640_: u8 = 0;
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut v_node_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v___x_3652_: usize = 0;
    let mut v___x_3653_: usize = 0;
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3658_: u8 = 0;
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3660_: u8 = 0;
    let mut v_unused_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3671_: u8 = 0;
    let mut v_ks_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: usize = 0;
    let mut v___x_3678_: u8 = 0;
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v_reuseFailAlloc_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3611_) == 0 {
                    v_es_3616_ = lean_ctor_get(v_x_3611_, 0);
                    v___x_3617_ = 5usize;
                    v___x_3618_ = 1usize;
                    v___x_3619_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__1);
                    v___x_3620_ = lean_usize_land(v_x_3612_, v___x_3619_);
                    v_j_3621_ = lean_usize_to_nat(v___x_3620_);
                    v___x_3622_ = lean_array_get_size(v_es_3616_);
                    v___x_3623_ = lean_nat_dec_lt(v_j_3621_, v___x_3622_);
                    if v___x_3623_ == 0 {
                        lean_dec(v_j_3621_);
                        lean_dec(v_x_3615_);
                        lean_dec(v_x_3614_);
                        return v_x_3611_;
                    } else {
                        lean_inc_ref(v_es_3616_);
                        v_isSharedCheck_3660_ = (!lean_is_exclusive(v_x_3611_)) as u8;
                        if v_isSharedCheck_3660_ == 0 {
                            v_unused_3661_ = lean_ctor_get(v_x_3611_, 0);
                            lean_dec(v_unused_3661_);
                            v___x_3625_ = v_x_3611_;
                            v_isShared_3626_ = v_isSharedCheck_3660_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3611_);
                            v___x_3625_ = lean_box(0);
                            v_isShared_3626_ = v_isSharedCheck_3660_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3662_ = lean_ctor_get(v_x_3611_, 0);
                    v_vs_3663_ = lean_ctor_get(v_x_3611_, 1);
                    v_isSharedCheck_3683_ = (!lean_is_exclusive(v_x_3611_)) as u8;
                    if v_isSharedCheck_3683_ == 0 {
                        v___x_3665_ = v_x_3611_;
                        v_isShared_3666_ = v_isSharedCheck_3683_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3663_);
                        lean_inc(v_ks_3662_);
                        lean_dec(v_x_3611_);
                        v___x_3665_ = lean_box(0);
                        v_isShared_3666_ = v_isSharedCheck_3683_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3627_ = lean_array_fget(v_es_3616_, v_j_3621_);
                v___x_3628_ = lean_box(0);
                v_xs_x27_3629_ = lean_array_fset(v_es_3616_, v_j_3621_, v___x_3628_);
                match lean_obj_tag(v_v_3627_) {
                    0 => {
                        v_key_3636_ = lean_ctor_get(v_v_3627_, 0);
                        v_val_3637_ = lean_ctor_get(v_v_3627_, 1);
                        v_isSharedCheck_3647_ = (!lean_is_exclusive(v_v_3627_)) as u8;
                        if v_isSharedCheck_3647_ == 0 {
                            v___x_3639_ = v_v_3627_;
                            v_isShared_3640_ = v_isSharedCheck_3647_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3637_);
                            lean_inc(v_key_3636_);
                            lean_dec(v_v_3627_);
                            v___x_3639_ = lean_box(0);
                            v_isShared_3640_ = v_isSharedCheck_3647_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3648_ = lean_ctor_get(v_v_3627_, 0);
                        v_isSharedCheck_3658_ = (!lean_is_exclusive(v_v_3627_)) as u8;
                        if v_isSharedCheck_3658_ == 0 {
                            v___x_3650_ = v_v_3627_;
                            v_isShared_3651_ = v_isSharedCheck_3658_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3648_);
                            lean_dec(v_v_3627_);
                            v___x_3650_ = lean_box(0);
                            v_isShared_3651_ = v_isSharedCheck_3658_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3659_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3659_, 0, v_x_3614_);
                        lean_ctor_set(v___x_3659_, 1, v_x_3615_);
                        v___y_3631_ = v___x_3659_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3632_ = lean_array_fset(v_xs_x27_3629_, v_j_3621_, v___y_3631_);
                lean_dec(v_j_3621_);
                if v_isShared_3626_ == 0 {
                    lean_ctor_set(v___x_3625_, 0, v___x_3632_);
                    v___x_3634_ = v___x_3625_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
                    v___x_3634_ = v_reuseFailAlloc_3635_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3634_;
            }
            4 => {
                v___x_3641_ = l_Lean_instBEqMVarId_beq(v_x_3614_, v_key_3636_);
                if v___x_3641_ == 0 {
                    lean_del_object(v___x_3639_);
                    v___x_3642_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3636_,
                        v_val_3637_,
                        v_x_3614_,
                        v_x_3615_,
                    );
                    v___x_3643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3643_, 0, v___x_3642_);
                    v___y_3631_ = v___x_3643_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3637_);
                    lean_dec(v_key_3636_);
                    if v_isShared_3640_ == 0 {
                        lean_ctor_set(v___x_3639_, 1, v_x_3615_);
                        lean_ctor_set(v___x_3639_, 0, v_x_3614_);
                        v___x_3645_ = v___x_3639_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_x_3614_);
                        lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_x_3615_);
                        v___x_3645_ = v_reuseFailAlloc_3646_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3631_ = v___x_3645_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3652_ = lean_usize_shift_right(v_x_3612_, v___x_3617_);
                v___x_3653_ = lean_usize_add(v_x_3613_, v___x_3618_);
                v___x_3654_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_node_3648_, v___x_3652_, v___x_3653_, v_x_3614_, v_x_3615_);
                if v_isShared_3651_ == 0 {
                    lean_ctor_set(v___x_3650_, 0, v___x_3654_);
                    v___x_3656_ = v___x_3650_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
                    v___x_3656_ = v_reuseFailAlloc_3657_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3631_ = v___x_3656_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3666_ == 0 {
                    v___x_3668_ = v___x_3665_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_ks_3662_);
                    lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_vs_3663_);
                    v___x_3668_ = v_reuseFailAlloc_3682_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3669_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v___x_3668_, v_x_3614_, v_x_3615_);
                v___x_3677_ = 7usize;
                v___x_3678_ = lean_usize_dec_le(v___x_3677_, v_x_3613_);
                if v___x_3678_ == 0 {
                    v___x_3679_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3669_);
                    v___x_3680_ = lean_unsigned_to_nat(4);
                    v___x_3681_ = lean_nat_dec_lt(v___x_3679_, v___x_3680_);
                    lean_dec(v___x_3679_);
                    v___y_3671_ = v___x_3681_;
                    state = 10;
                    continue;
                } else {
                    v___y_3671_ = v___x_3678_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3671_ == 0 {
                    v_ks_3672_ = lean_ctor_get(v_newNode_3669_, 0);
                    lean_inc_ref(v_ks_3672_);
                    v_vs_3673_ = lean_ctor_get(v_newNode_3669_, 1);
                    lean_inc_ref(v_vs_3673_);
                    lean_dec_ref(v_newNode_3669_);
                    v___x_3674_ = lean_unsigned_to_nat(0);
                    v___x_3675_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___closed__2);
                    v___x_3676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_x_3613_, v_ks_3672_, v_vs_3673_, v___x_3674_, v___x_3675_);
                    lean_dec_ref(v_vs_3673_);
                    lean_dec_ref(v_ks_3672_);
                    return v___x_3676_;
                } else {
                    return v_newNode_3669_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(
    mut v_depth_3684_: usize,
    mut v_keys_3685_: *mut LeanObject,
    mut v_vals_3686_: *mut LeanObject,
    mut v_i_3687_: *mut LeanObject,
    mut v_entries_3688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: u8 = 0;
    let mut v_k_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: u64 = 0;
    let mut v_h_3694_: usize = 0;
    let mut v___x_3695_: usize = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: usize = 0;
    let mut v___x_3698_: usize = 0;
    let mut v___x_3699_: usize = 0;
    let mut v_h_3700_: usize = 0;
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3689_ = lean_array_get_size(v_keys_3685_);
                v___x_3690_ = lean_nat_dec_lt(v_i_3687_, v___x_3689_);
                if v___x_3690_ == 0 {
                    lean_dec(v_i_3687_);
                    return v_entries_3688_;
                } else {
                    v_k_3691_ = lean_array_fget_borrowed(v_keys_3685_, v_i_3687_);
                    v_v_3692_ = lean_array_fget_borrowed(v_vals_3686_, v_i_3687_);
                    v___x_3693_ = l_Lean_instHashableMVarId_hash(v_k_3691_);
                    v_h_3694_ = lean_uint64_to_usize(v___x_3693_);
                    v___x_3695_ = 5usize;
                    v___x_3696_ = lean_unsigned_to_nat(1);
                    v___x_3697_ = 1usize;
                    v___x_3698_ = lean_usize_sub(v_depth_3684_, v___x_3697_);
                    v___x_3699_ = lean_usize_mul(v___x_3695_, v___x_3698_);
                    v_h_3700_ = lean_usize_shift_right(v_h_3694_, v___x_3699_);
                    v___x_3701_ = lean_nat_add(v_i_3687_, v___x_3696_);
                    lean_dec(v_i_3687_);
                    lean_inc(v_v_3692_);
                    lean_inc(v_k_3691_);
                    v___x_3702_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_entries_3688_, v_h_3700_, v_depth_3684_, v_k_3691_, v_v_3692_);
                    v_i_3687_ = v___x_3701_;
                    v_entries_3688_ = v___x_3702_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg___boxed(
    mut v_depth_3704_: *mut LeanObject,
    mut v_keys_3705_: *mut LeanObject,
    mut v_vals_3706_: *mut LeanObject,
    mut v_i_3707_: *mut LeanObject,
    mut v_entries_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3709_: usize = 0;
    let mut v_res_3710_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3709_ = lean_unbox_usize(v_depth_3704_);
    lean_dec(v_depth_3704_);
    v_res_3710_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_boxed_3709_, v_keys_3705_, v_vals_3706_, v_i_3707_, v_entries_3708_);
    lean_dec_ref(v_vals_3706_);
    lean_dec_ref(v_keys_3705_);
    return v_res_3710_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg___boxed(
    mut v_x_3711_: *mut LeanObject,
    mut v_x_3712_: *mut LeanObject,
    mut v_x_3713_: *mut LeanObject,
    mut v_x_3714_: *mut LeanObject,
    mut v_x_3715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_8577__boxed_3716_: usize = 0;
    let mut v_x_8578__boxed_3717_: usize = 0;
    let mut v_res_3718_: *mut LeanObject = core::ptr::null_mut();
    v_x_8577__boxed_3716_ = lean_unbox_usize(v_x_3712_);
    lean_dec(v_x_3712_);
    v_x_8578__boxed_3717_ = lean_unbox_usize(v_x_3713_);
    lean_dec(v_x_3713_);
    v_res_3718_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_3711_, v_x_8577__boxed_3716_, v_x_8578__boxed_3717_, v_x_3714_, v_x_3715_);
    return v_res_3718_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(
    mut v_x_3719_: *mut LeanObject,
    mut v_x_3720_: *mut LeanObject,
    mut v_x_3721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3722_: u64 = 0;
    let mut v___x_3723_: usize = 0;
    let mut v___x_3724_: usize = 0;
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    v___x_3722_ = l_Lean_instHashableMVarId_hash(v_x_3720_);
    v___x_3723_ = lean_uint64_to_usize(v___x_3722_);
    v___x_3724_ = 1usize;
    v___x_3725_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_3719_, v___x_3723_, v___x_3724_, v_x_3720_, v_x_3721_);
    return v___x_3725_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(
    mut v_mvarId_3726_: *mut LeanObject,
    mut v_val_3727_: *mut LeanObject,
    mut v___y_3728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v_depth_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3751_: u8 = 0;
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3762_: u8 = 0;
    let mut v_isSharedCheck_3763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3730_ = lean_st_ref_take(v___y_3728_);
                v_mctx_3731_ = lean_ctor_get(v___x_3730_, 0);
                v_cache_3732_ = lean_ctor_get(v___x_3730_, 1);
                v_zetaDeltaFVarIds_3733_ = lean_ctor_get(v___x_3730_, 2);
                v_postponed_3734_ = lean_ctor_get(v___x_3730_, 3);
                v_diag_3735_ = lean_ctor_get(v___x_3730_, 4);
                v_isSharedCheck_3763_ = (!lean_is_exclusive(v___x_3730_)) as u8;
                if v_isSharedCheck_3763_ == 0 {
                    v___x_3737_ = v___x_3730_;
                    v_isShared_3738_ = v_isSharedCheck_3763_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3735_);
                    lean_inc(v_postponed_3734_);
                    lean_inc(v_zetaDeltaFVarIds_3733_);
                    lean_inc(v_cache_3732_);
                    lean_inc(v_mctx_3731_);
                    lean_dec(v___x_3730_);
                    v___x_3737_ = lean_box(0);
                    v_isShared_3738_ = v_isSharedCheck_3763_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3739_ = lean_ctor_get(v_mctx_3731_, 0);
                v_levelAssignDepth_3740_ = lean_ctor_get(v_mctx_3731_, 1);
                v_lmvarCounter_3741_ = lean_ctor_get(v_mctx_3731_, 2);
                v_mvarCounter_3742_ = lean_ctor_get(v_mctx_3731_, 3);
                v_lDecls_3743_ = lean_ctor_get(v_mctx_3731_, 4);
                v_decls_3744_ = lean_ctor_get(v_mctx_3731_, 5);
                v_userNames_3745_ = lean_ctor_get(v_mctx_3731_, 6);
                v_lAssignment_3746_ = lean_ctor_get(v_mctx_3731_, 7);
                v_eAssignment_3747_ = lean_ctor_get(v_mctx_3731_, 8);
                v_dAssignment_3748_ = lean_ctor_get(v_mctx_3731_, 9);
                v_isSharedCheck_3762_ = (!lean_is_exclusive(v_mctx_3731_)) as u8;
                if v_isSharedCheck_3762_ == 0 {
                    v___x_3750_ = v_mctx_3731_;
                    v_isShared_3751_ = v_isSharedCheck_3762_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_3748_);
                    lean_inc(v_eAssignment_3747_);
                    lean_inc(v_lAssignment_3746_);
                    lean_inc(v_userNames_3745_);
                    lean_inc(v_decls_3744_);
                    lean_inc(v_lDecls_3743_);
                    lean_inc(v_mvarCounter_3742_);
                    lean_inc(v_lmvarCounter_3741_);
                    lean_inc(v_levelAssignDepth_3740_);
                    lean_inc(v_depth_3739_);
                    lean_dec(v_mctx_3731_);
                    v___x_3750_ = lean_box(0);
                    v_isShared_3751_ = v_isSharedCheck_3762_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3752_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_eAssignment_3747_, v_mvarId_3726_, v_val_3727_);
                if v_isShared_3751_ == 0 {
                    lean_ctor_set(v___x_3750_, 8, v___x_3752_);
                    v___x_3754_ = v___x_3750_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_depth_3739_);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_levelAssignDepth_3740_);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_lmvarCounter_3741_);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_mvarCounter_3742_);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 4, v_lDecls_3743_);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 5, v_decls_3744_);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 6, v_userNames_3745_);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 7, v_lAssignment_3746_);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 8, v___x_3752_);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 9, v_dAssignment_3748_);
                    v___x_3754_ = v_reuseFailAlloc_3761_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3738_ == 0 {
                    lean_ctor_set(v___x_3737_, 0, v___x_3754_);
                    v___x_3756_ = v___x_3737_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3754_);
                    lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_cache_3732_);
                    lean_ctor_set(v_reuseFailAlloc_3760_, 2, v_zetaDeltaFVarIds_3733_);
                    lean_ctor_set(v_reuseFailAlloc_3760_, 3, v_postponed_3734_);
                    lean_ctor_set(v_reuseFailAlloc_3760_, 4, v_diag_3735_);
                    v___x_3756_ = v_reuseFailAlloc_3760_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3757_ = lean_st_ref_set(v___y_3728_, v___x_3756_);
                v___x_3758_ = lean_box(0);
                v___x_3759_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3759_, 0, v___x_3758_);
                return v___x_3759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg___boxed(
    mut v_mvarId_3764_: *mut LeanObject,
    mut v_val_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
    mut v___y_3767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3768_: *mut LeanObject = core::ptr::null_mut();
    v_res_3768_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_3764_, v_val_3765_, v___y_3766_);
    lean_dec(v___y_3766_);
    return v_res_3768_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    v___x_3772_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__2;
    v___x_3773_ = lean_unsigned_to_nat(33);
    v___x_3774_ = lean_unsigned_to_nat(105);
    v___x_3775_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__1;
    v___x_3776_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15;
    v___x_3777_ = l_mkPanicMessageWithDecl(
        v___x_3776_,
        v___x_3775_,
        v___x_3774_,
        v___x_3773_,
        v___x_3772_,
    );
    return v___x_3777_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    v___x_3779_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__4;
    v___x_3780_ = l_Lean_stringToMessageData(v___x_3779_);
    return v___x_3780_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    v___x_3782_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__6;
    v___x_3783_ = l_Lean_stringToMessageData(v___x_3782_);
    return v___x_3783_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(
    mut v___x_3784_: *mut LeanObject,
    mut v_snd_3785_: *mut LeanObject,
    mut v_hyp_3786_: *mut LeanObject,
    mut v___x_3787_: *mut LeanObject,
    mut v_args_3788_: *mut LeanObject,
    mut v_fst_3789_: *mut LeanObject,
    mut v___y_3790_: *mut LeanObject,
    mut v___y_3791_: *mut LeanObject,
    mut v___y_3792_: *mut LeanObject,
    mut v___y_3793_: *mut LeanObject,
    mut v___y_3794_: *mut LeanObject,
    mut v___y_3795_: *mut LeanObject,
    mut v___y_3796_: *mut LeanObject,
    mut v___y_3797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restHyps_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v___x_3812_: u8 = 0;
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3825_: usize = 0;
    let mut v___x_3826_: usize = 0;
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3833_: u8 = 0;
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3855_: u8 = 0;
    let mut v_reuseFailAlloc_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3857_: u8 = 0;
    let mut v_a_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3865_: u8 = 0;
    let mut v_isSharedCheck_3866_: u8 = 0;
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___x_3784_) == 1 {
                    v_val_3799_ = lean_ctor_get(v___x_3784_, 0);
                    lean_inc(v_val_3799_);
                    lean_dec_ref_known(v___x_3784_, 1);
                    v_focusHyp_3800_ = lean_ctor_get(v_val_3799_, 0);
                    lean_inc_ref_n(v_focusHyp_3800_, 2);
                    v_restHyps_3801_ = lean_ctor_get(v_val_3799_, 1);
                    lean_inc_ref(v_restHyps_3801_);
                    v_proof_3802_ = lean_ctor_get(v_val_3799_, 2);
                    lean_inc_ref(v_proof_3802_);
                    lean_dec(v_val_3799_);
                    v___x_3803_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_3800_);
                    if lean_obj_tag(v___x_3803_) == 1 {
                        v_val_3804_ = lean_ctor_get(v___x_3803_, 0);
                        lean_inc(v_val_3804_);
                        lean_dec_ref_known(v___x_3803_, 1);
                        v_u_3805_ = lean_ctor_get(v_snd_3785_, 0);
                        v_00_u03c3s_3806_ = lean_ctor_get(v_snd_3785_, 1);
                        v_hyps_3807_ = lean_ctor_get(v_snd_3785_, 2);
                        v_target_3808_ = lean_ctor_get(v_snd_3785_, 3);
                        v_isSharedCheck_3866_ = (!lean_is_exclusive(v_snd_3785_)) as u8;
                        if v_isSharedCheck_3866_ == 0 {
                            v___x_3810_ = v_snd_3785_;
                            v_isShared_3811_ = v_isSharedCheck_3866_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_target_3808_);
                            lean_inc(v_hyps_3807_);
                            lean_inc(v_00_u03c3s_3806_);
                            lean_inc(v_u_3805_);
                            lean_dec(v_snd_3785_);
                            v___x_3810_ = lean_box(0);
                            v_isShared_3811_ = v_isSharedCheck_3866_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3803_);
                        lean_dec_ref(v_proof_3802_);
                        lean_dec_ref(v_restHyps_3801_);
                        lean_dec_ref(v_focusHyp_3800_);
                        lean_dec(v_fst_3789_);
                        lean_dec_ref(v___x_3787_);
                        lean_dec(v_hyp_3786_);
                        lean_dec_ref(v_snd_3785_);
                        v___x_3867_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__3);
                        v___x_3868_ =
                            l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(
                                v___x_3867_,
                                v___y_3790_,
                                v___y_3791_,
                                v___y_3792_,
                                v___y_3793_,
                                v___y_3794_,
                                v___y_3795_,
                                v___y_3796_,
                                v___y_3797_,
                            );
                        return v___x_3868_;
                    }
                } else {
                    lean_dec(v_fst_3789_);
                    lean_dec_ref(v___x_3787_);
                    lean_dec_ref(v_snd_3785_);
                    lean_dec(v___x_3784_);
                    v___x_3869_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__5);
                    v___x_3870_ = l_Lean_MessageData_ofSyntax(v_hyp_3786_);
                    v___x_3871_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3871_, 0, v___x_3869_);
                    lean_ctor_set(v___x_3871_, 1, v___x_3870_);
                    v___x_3872_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__7);
                    v___x_3873_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3873_, 0, v___x_3871_);
                    lean_ctor_set(v___x_3873_, 1, v___x_3872_);
                    v___x_3874_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_3873_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
                    return v___x_3874_;
                }
            }
            1 => {
                v___x_3812_ = 0;
                lean_inc_ref(v_00_u03c3s_3806_);
                v___x_3813_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                    v_hyp_3786_,
                    v_00_u03c3s_3806_,
                    v_val_3804_,
                    v___x_3812_,
                    v___y_3794_,
                    v___y_3795_,
                    v___y_3796_,
                    v___y_3797_,
                );
                if lean_obj_tag(v___x_3813_) == 0 {
                    lean_dec_ref_known(v___x_3813_, 1);
                    v___x_3814_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0;
                    v___x_3815_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                    v___x_3816_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1;
                    v___x_3817_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                    v___x_3818_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___closed__0;
                    v___x_3819_ = l_Lean_Name_mkStr6(
                        v___x_3814_,
                        v___x_3815_,
                        v___x_3816_,
                        v___x_3787_,
                        v___x_3817_,
                        v___x_3818_,
                    );
                    v___x_3820_ = lean_box(0);
                    lean_inc_n(v_u_3805_, 2);
                    v___x_3821_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3821_, 0, v_u_3805_);
                    lean_ctor_set(v___x_3821_, 1, v___x_3820_);
                    lean_inc_ref(v___x_3821_);
                    v___x_3822_ = l_Lean_mkConst(v___x_3819_, v___x_3821_);
                    lean_inc_ref_n(v_target_3808_, 2);
                    lean_inc_ref(v_focusHyp_3800_);
                    lean_inc_ref_n(v_restHyps_3801_, 2);
                    lean_inc_ref_n(v_00_u03c3s_3806_, 2);
                    v___x_3823_ = lean_alloc_closure(l_Lean_mkApp7 as *mut core::ffi::c_void, 8, 7);
                    lean_closure_set(v___x_3823_, 0, v___x_3822_);
                    lean_closure_set(v___x_3823_, 1, v_00_u03c3s_3806_);
                    lean_closure_set(v___x_3823_, 2, v_hyps_3807_);
                    lean_closure_set(v___x_3823_, 3, v_restHyps_3801_);
                    lean_closure_set(v___x_3823_, 4, v_focusHyp_3800_);
                    lean_closure_set(v___x_3823_, 5, v_target_3808_);
                    lean_closure_set(v___x_3823_, 6, v_proof_3802_);
                    v___x_3824_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3824_, 0, v_focusHyp_3800_);
                    lean_ctor_set(v___x_3824_, 1, v___x_3823_);
                    v_sz_3825_ = lean_array_size(v_args_3788_);
                    v___x_3826_ = 0usize;
                    v___x_3827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1(v___x_3821_, v_u_3805_, v_00_u03c3s_3806_, v_restHyps_3801_, v_target_3808_, v_args_3788_, v_sz_3825_, v___x_3826_, v___x_3824_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
                    if lean_obj_tag(v___x_3827_) == 0 {
                        v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
                        lean_inc(v_a_3828_);
                        lean_dec_ref_known(v___x_3827_, 1);
                        v_fst_3829_ = lean_ctor_get(v_a_3828_, 0);
                        v_snd_3830_ = lean_ctor_get(v_a_3828_, 1);
                        v_isSharedCheck_3857_ = (!lean_is_exclusive(v_a_3828_)) as u8;
                        if v_isSharedCheck_3857_ == 0 {
                            v___x_3832_ = v_a_3828_;
                            v_isShared_3833_ = v_isSharedCheck_3857_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_3830_);
                            lean_inc(v_fst_3829_);
                            lean_dec(v_a_3828_);
                            v___x_3832_ = lean_box(0);
                            v_isShared_3833_ = v_isSharedCheck_3857_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3810_);
                        lean_dec_ref(v_target_3808_);
                        lean_dec_ref(v_00_u03c3s_3806_);
                        lean_dec(v_u_3805_);
                        lean_dec_ref(v_restHyps_3801_);
                        lean_dec(v_fst_3789_);
                        v_a_3858_ = lean_ctor_get(v___x_3827_, 0);
                        v_isSharedCheck_3865_ = (!lean_is_exclusive(v___x_3827_)) as u8;
                        if v_isSharedCheck_3865_ == 0 {
                            v___x_3860_ = v___x_3827_;
                            v_isShared_3861_ = v_isSharedCheck_3865_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3858_);
                            lean_dec(v___x_3827_);
                            v___x_3860_ = lean_box(0);
                            v_isShared_3861_ = v_isSharedCheck_3865_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3810_);
                    lean_dec_ref(v_target_3808_);
                    lean_dec_ref(v_hyps_3807_);
                    lean_dec_ref(v_00_u03c3s_3806_);
                    lean_dec(v_u_3805_);
                    lean_dec_ref(v_proof_3802_);
                    lean_dec_ref(v_restHyps_3801_);
                    lean_dec_ref(v_focusHyp_3800_);
                    lean_dec(v_fst_3789_);
                    lean_dec_ref(v___x_3787_);
                    return v___x_3813_;
                }
            }
            2 => {
                lean_inc_ref(v_00_u03c3s_3806_);
                lean_inc(v_u_3805_);
                v___x_3834_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_3805_,
                    v_00_u03c3s_3806_,
                    v_restHyps_3801_,
                    v_fst_3829_,
                );
                if v_isShared_3811_ == 0 {
                    lean_ctor_set(v___x_3810_, 2, v___x_3834_);
                    v___x_3836_ = v___x_3810_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_u_3805_);
                    lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_00_u03c3s_3806_);
                    lean_ctor_set(v_reuseFailAlloc_3856_, 2, v___x_3834_);
                    lean_ctor_set(v_reuseFailAlloc_3856_, 3, v_target_3808_);
                    v___x_3836_ = v_reuseFailAlloc_3856_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3837_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_3836_);
                v___x_3838_ = lean_box(0);
                v___x_3839_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_3837_,
                    v___x_3838_,
                    v___y_3794_,
                    v___y_3795_,
                    v___y_3796_,
                    v___y_3797_,
                );
                if lean_obj_tag(v___x_3839_) == 0 {
                    v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
                    lean_inc_n(v_a_3840_, 2);
                    lean_dec_ref_known(v___x_3839_, 1);
                    v___x_3841_ = lean_apply_1(v_snd_3830_, v_a_3840_);
                    v___x_3842_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_3789_, v___x_3841_, v___y_3795_);
                    lean_dec_ref(v___x_3842_);
                    v___x_3843_ = l_Lean_Expr_mvarId_x21(v_a_3840_);
                    lean_dec(v_a_3840_);
                    if v_isShared_3833_ == 0 {
                        lean_ctor_set_tag(v___x_3832_, 1);
                        lean_ctor_set(v___x_3832_, 1, v___x_3820_);
                        lean_ctor_set(v___x_3832_, 0, v___x_3843_);
                        v___x_3845_ = v___x_3832_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3843_);
                        lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___x_3820_);
                        v___x_3845_ = v_reuseFailAlloc_3847_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3832_);
                    lean_dec(v_snd_3830_);
                    lean_dec(v_fst_3789_);
                    v_a_3848_ = lean_ctor_get(v___x_3839_, 0);
                    v_isSharedCheck_3855_ = (!lean_is_exclusive(v___x_3839_)) as u8;
                    if v_isSharedCheck_3855_ == 0 {
                        v___x_3850_ = v___x_3839_;
                        v_isShared_3851_ = v_isSharedCheck_3855_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3848_);
                        lean_dec(v___x_3839_);
                        v___x_3850_ = lean_box(0);
                        v_isShared_3851_ = v_isSharedCheck_3855_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3846_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_3845_,
                    v___y_3791_,
                    v___y_3794_,
                    v___y_3795_,
                    v___y_3796_,
                    v___y_3797_,
                );
                return v___x_3846_;
            }
            5 => {
                if v_isShared_3851_ == 0 {
                    v___x_3853_ = v___x_3850_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
                    v___x_3853_ = v_reuseFailAlloc_3854_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3853_;
            }
            7 => {
                if v_isShared_3861_ == 0 {
                    v___x_3863_ = v___x_3860_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
                    v___x_3863_ = v_reuseFailAlloc_3864_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed(
    mut v___x_3875_: *mut LeanObject,
    mut v_snd_3876_: *mut LeanObject,
    mut v_hyp_3877_: *mut LeanObject,
    mut v___x_3878_: *mut LeanObject,
    mut v_args_3879_: *mut LeanObject,
    mut v_fst_3880_: *mut LeanObject,
    mut v___y_3881_: *mut LeanObject,
    mut v___y_3882_: *mut LeanObject,
    mut v___y_3883_: *mut LeanObject,
    mut v___y_3884_: *mut LeanObject,
    mut v___y_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
    mut v___y_3888_: *mut LeanObject,
    mut v___y_3889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3890_: *mut LeanObject = core::ptr::null_mut();
    v_res_3890_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0(
        v___x_3875_,
        v_snd_3876_,
        v_hyp_3877_,
        v___x_3878_,
        v_args_3879_,
        v_fst_3880_,
        v___y_3881_,
        v___y_3882_,
        v___y_3883_,
        v___y_3884_,
        v___y_3885_,
        v___y_3886_,
        v___y_3887_,
        v___y_3888_,
    );
    lean_dec(v___y_3888_);
    lean_dec_ref(v___y_3887_);
    lean_dec(v___y_3886_);
    lean_dec_ref(v___y_3885_);
    lean_dec(v___y_3884_);
    lean_dec_ref(v___y_3883_);
    lean_dec(v___y_3882_);
    lean_dec_ref(v___y_3881_);
    lean_dec_ref(v_args_3879_);
    return v_res_3890_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(
    mut v_x_3898_: *mut LeanObject,
    mut v_a_3899_: *mut LeanObject,
    mut v_a_3900_: *mut LeanObject,
    mut v_a_3901_: *mut LeanObject,
    mut v_a_3902_: *mut LeanObject,
    mut v_a_3903_: *mut LeanObject,
    mut v_a_3904_: *mut LeanObject,
    mut v_a_3905_: *mut LeanObject,
    mut v_a_3906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: u8 = 0;
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyp_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3908_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                v___x_3909_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2;
                lean_inc(v_x_3898_);
                v___x_3910_ = l_Lean_Syntax_isOfKind(v_x_3898_, v___x_3909_);
                if v___x_3910_ == 0 {
                    lean_dec(v_x_3898_);
                    v___x_3911_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
                    return v___x_3911_;
                } else {
                    v___x_3912_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                        v_a_3900_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_,
                    );
                    if lean_obj_tag(v___x_3912_) == 0 {
                        v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
                        lean_inc(v_a_3913_);
                        lean_dec_ref_known(v___x_3912_, 1);
                        v_fst_3914_ = lean_ctor_get(v_a_3913_, 0);
                        lean_inc_n(v_fst_3914_, 2);
                        v_snd_3915_ = lean_ctor_get(v_a_3913_, 1);
                        lean_inc_n(v_snd_3915_, 2);
                        lean_dec(v_a_3913_);
                        v___x_3916_ = lean_unsigned_to_nat(1);
                        v_hyp_3917_ = l_Lean_Syntax_getArg(v_x_3898_, v___x_3916_);
                        v___x_3918_ = lean_unsigned_to_nat(2);
                        v___x_3919_ = l_Lean_Syntax_getArg(v_x_3898_, v___x_3918_);
                        lean_dec(v_x_3898_);
                        v_args_3920_ = l_Lean_Syntax_getArgs(v___x_3919_);
                        lean_dec(v___x_3919_);
                        v___x_3921_ = l_Lean_TSyntax_getId(v_hyp_3917_);
                        v___x_3922_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(
                            v_snd_3915_,
                            v___x_3921_,
                        );
                        lean_dec(v___x_3921_);
                        v___y_3923_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___lam__0___boxed
                                as *mut core::ffi::c_void,
                            15,
                            6,
                        );
                        lean_closure_set(v___y_3923_, 0, v___x_3922_);
                        lean_closure_set(v___y_3923_, 1, v_snd_3915_);
                        lean_closure_set(v___y_3923_, 2, v_hyp_3917_);
                        lean_closure_set(v___y_3923_, 3, v___x_3908_);
                        lean_closure_set(v___y_3923_, 4, v_args_3920_);
                        lean_closure_set(v___y_3923_, 5, v_fst_3914_);
                        v___x_3924_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_3914_, v___y_3923_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
                        return v___x_3924_;
                    } else {
                        lean_dec(v_x_3898_);
                        v_a_3925_ = lean_ctor_get(v___x_3912_, 0);
                        v_isSharedCheck_3932_ = (!lean_is_exclusive(v___x_3912_)) as u8;
                        if v_isSharedCheck_3932_ == 0 {
                            v___x_3927_ = v___x_3912_;
                            v_isShared_3928_ = v_isSharedCheck_3932_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3925_);
                            lean_dec(v___x_3912_);
                            v___x_3927_ = lean_box(0);
                            v_isShared_3928_ = v_isSharedCheck_3932_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3928_ == 0 {
                    v___x_3930_ = v___x_3927_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
                    v___x_3930_ = v_reuseFailAlloc_3931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed(
    mut v_x_3933_: *mut LeanObject,
    mut v_a_3934_: *mut LeanObject,
    mut v_a_3935_: *mut LeanObject,
    mut v_a_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
    mut v_a_3941_: *mut LeanObject,
    mut v_a_3942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3943_: *mut LeanObject = core::ptr::null_mut();
    v_res_3943_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize(
        v_x_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_,
        v_a_3941_,
    );
    lean_dec(v_a_3941_);
    lean_dec_ref(v_a_3940_);
    lean_dec(v_a_3939_);
    lean_dec_ref(v_a_3938_);
    lean_dec(v_a_3937_);
    lean_dec_ref(v_a_3936_);
    lean_dec(v_a_3935_);
    lean_dec_ref(v_a_3934_);
    return v_res_3943_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(
    mut v_mvarId_3944_: *mut LeanObject,
    mut v_val_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
    mut v___y_3947_: *mut LeanObject,
    mut v___y_3948_: *mut LeanObject,
    mut v___y_3949_: *mut LeanObject,
    mut v___y_3950_: *mut LeanObject,
    mut v___y_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    v___x_3955_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_mvarId_3944_, v_val_3945_, v___y_3951_);
    return v___x_3955_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___boxed(
    mut v_mvarId_3956_: *mut LeanObject,
    mut v_val_3957_: *mut LeanObject,
    mut v___y_3958_: *mut LeanObject,
    mut v___y_3959_: *mut LeanObject,
    mut v___y_3960_: *mut LeanObject,
    mut v___y_3961_: *mut LeanObject,
    mut v___y_3962_: *mut LeanObject,
    mut v___y_3963_: *mut LeanObject,
    mut v___y_3964_: *mut LeanObject,
    mut v___y_3965_: *mut LeanObject,
    mut v___y_3966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3967_: *mut LeanObject = core::ptr::null_mut();
    v_res_3967_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2(
            v_mvarId_3956_,
            v_val_3957_,
            v___y_3958_,
            v___y_3959_,
            v___y_3960_,
            v___y_3961_,
            v___y_3962_,
            v___y_3963_,
            v___y_3964_,
            v___y_3965_,
        );
    lean_dec(v___y_3965_);
    lean_dec_ref(v___y_3964_);
    lean_dec(v___y_3963_);
    lean_dec_ref(v___y_3962_);
    lean_dec(v___y_3961_);
    lean_dec_ref(v___y_3960_);
    lean_dec(v___y_3959_);
    lean_dec_ref(v___y_3958_);
    return v_res_3967_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2(
    mut v_00_u03b2_3968_: *mut LeanObject,
    mut v_x_3969_: *mut LeanObject,
    mut v_x_3970_: *mut LeanObject,
    mut v_x_3971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    v___x_3972_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2___redArg(v_x_3969_, v_x_3970_, v_x_3971_);
    return v___x_3972_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(
    mut v_00_u03b2_3973_: *mut LeanObject,
    mut v_x_3974_: *mut LeanObject,
    mut v_x_3975_: usize,
    mut v_x_3976_: usize,
    mut v_x_3977_: *mut LeanObject,
    mut v_x_3978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    v___x_3979_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___redArg(v_x_3974_, v_x_3975_, v_x_3976_, v_x_3977_, v_x_3978_);
    return v___x_3979_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5___boxed(
    mut v_00_u03b2_3980_: *mut LeanObject,
    mut v_x_3981_: *mut LeanObject,
    mut v_x_3982_: *mut LeanObject,
    mut v_x_3983_: *mut LeanObject,
    mut v_x_3984_: *mut LeanObject,
    mut v_x_3985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9134__boxed_3986_: usize = 0;
    let mut v_x_9135__boxed_3987_: usize = 0;
    let mut v_res_3988_: *mut LeanObject = core::ptr::null_mut();
    v_x_9134__boxed_3986_ = lean_unbox_usize(v_x_3982_);
    lean_dec(v_x_3982_);
    v_x_9135__boxed_3987_ = lean_unbox_usize(v_x_3983_);
    lean_dec(v_x_3983_);
    v_res_3988_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5(v_00_u03b2_3980_, v_x_3981_, v_x_9134__boxed_3986_, v_x_9135__boxed_3987_, v_x_3984_, v_x_3985_);
    return v_res_3988_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6(
    mut v_00_u03b2_3989_: *mut LeanObject,
    mut v_n_3990_: *mut LeanObject,
    mut v_k_3991_: *mut LeanObject,
    mut v_v_3992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    v___x_3993_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6___redArg(v_n_3990_, v_k_3991_, v_v_3992_);
    return v___x_3993_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(
    mut v_00_u03b2_3994_: *mut LeanObject,
    mut v_depth_3995_: usize,
    mut v_keys_3996_: *mut LeanObject,
    mut v_vals_3997_: *mut LeanObject,
    mut v_heq_3998_: *mut LeanObject,
    mut v_i_3999_: *mut LeanObject,
    mut v_entries_4000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    v___x_4001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___redArg(v_depth_3995_, v_keys_3996_, v_vals_3997_, v_i_3999_, v_entries_4000_);
    return v___x_4001_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7___boxed(
    mut v_00_u03b2_4002_: *mut LeanObject,
    mut v_depth_4003_: *mut LeanObject,
    mut v_keys_4004_: *mut LeanObject,
    mut v_vals_4005_: *mut LeanObject,
    mut v_heq_4006_: *mut LeanObject,
    mut v_i_4007_: *mut LeanObject,
    mut v_entries_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4009_: usize = 0;
    let mut v_res_4010_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4009_ = lean_unbox_usize(v_depth_4003_);
    lean_dec(v_depth_4003_);
    v_res_4010_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__7(v_00_u03b2_4002_, v_depth_boxed_4009_, v_keys_4004_, v_vals_4005_, v_heq_4006_, v_i_4007_, v_entries_4008_);
    lean_dec_ref(v_vals_4005_);
    lean_dec_ref(v_keys_4004_);
    return v_res_4010_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7(
    mut v_00_u03b2_4011_: *mut LeanObject,
    mut v_x_4012_: *mut LeanObject,
    mut v_x_4013_: *mut LeanObject,
    mut v_x_4014_: *mut LeanObject,
    mut v_x_4015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    v___x_4016_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2_spec__2_spec__5_spec__6_spec__7___redArg(v_x_4012_, v_x_4013_, v_x_4014_, v_x_4015_);
    return v___x_4016_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1()
-> *mut LeanObject {
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    v___x_4026_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4027_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___closed__2;
    v___x_4028_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___closed__1;
    v___x_4029_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4030_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4026_,
        v___x_4027_,
        v___x_4028_,
        v___x_4029_,
    );
    return v___x_4030_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1___boxed(
    mut v_a_4031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4032_: *mut LeanObject = core::ptr::null_mut();
    v_res_4032_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
    return v_res_4032_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(
    mut v___y_4033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4053_: u8 = 0;
    let mut v_r_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4065_: u8 = 0;
    let mut v_unused_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4035_ = lean_st_ref_get(v___y_4033_);
                v_ngen_4036_ = lean_ctor_get(v___x_4035_, 2);
                lean_inc_ref(v_ngen_4036_);
                lean_dec(v___x_4035_);
                v_namePrefix_4037_ = lean_ctor_get(v_ngen_4036_, 0);
                v_idx_4038_ = lean_ctor_get(v_ngen_4036_, 1);
                v_isSharedCheck_4067_ = (!lean_is_exclusive(v_ngen_4036_)) as u8;
                if v_isSharedCheck_4067_ == 0 {
                    v___x_4040_ = v_ngen_4036_;
                    v_isShared_4041_ = v_isSharedCheck_4067_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_4038_);
                    lean_inc(v_namePrefix_4037_);
                    lean_dec(v_ngen_4036_);
                    v___x_4040_ = lean_box(0);
                    v_isShared_4041_ = v_isSharedCheck_4067_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4042_ = lean_st_ref_take(v___y_4033_);
                v_env_4043_ = lean_ctor_get(v___x_4042_, 0);
                v_nextMacroScope_4044_ = lean_ctor_get(v___x_4042_, 1);
                v_auxDeclNGen_4045_ = lean_ctor_get(v___x_4042_, 3);
                v_traceState_4046_ = lean_ctor_get(v___x_4042_, 4);
                v_cache_4047_ = lean_ctor_get(v___x_4042_, 5);
                v_messages_4048_ = lean_ctor_get(v___x_4042_, 6);
                v_infoState_4049_ = lean_ctor_get(v___x_4042_, 7);
                v_snapshotTasks_4050_ = lean_ctor_get(v___x_4042_, 8);
                v_isSharedCheck_4065_ = (!lean_is_exclusive(v___x_4042_)) as u8;
                if v_isSharedCheck_4065_ == 0 {
                    v_unused_4066_ = lean_ctor_get(v___x_4042_, 2);
                    lean_dec(v_unused_4066_);
                    v___x_4052_ = v___x_4042_;
                    v_isShared_4053_ = v_isSharedCheck_4065_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4050_);
                    lean_inc(v_infoState_4049_);
                    lean_inc(v_messages_4048_);
                    lean_inc(v_cache_4047_);
                    lean_inc(v_traceState_4046_);
                    lean_inc(v_auxDeclNGen_4045_);
                    lean_inc(v_nextMacroScope_4044_);
                    lean_inc(v_env_4043_);
                    lean_dec(v___x_4042_);
                    v___x_4052_ = lean_box(0);
                    v_isShared_4053_ = v_isSharedCheck_4065_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_idx_4038_);
                lean_inc(v_namePrefix_4037_);
                v_r_4054_ = l_Lean_Name_num___override(v_namePrefix_4037_, v_idx_4038_);
                v___x_4055_ = lean_unsigned_to_nat(1);
                v___x_4056_ = lean_nat_add(v_idx_4038_, v___x_4055_);
                lean_dec(v_idx_4038_);
                if v_isShared_4041_ == 0 {
                    lean_ctor_set(v___x_4040_, 1, v___x_4056_);
                    v___x_4058_ = v___x_4040_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_namePrefix_4037_);
                    lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_4056_);
                    v___x_4058_ = v_reuseFailAlloc_4064_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4053_ == 0 {
                    lean_ctor_set(v___x_4052_, 2, v___x_4058_);
                    v___x_4060_ = v___x_4052_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_env_4043_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_nextMacroScope_4044_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 2, v___x_4058_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 3, v_auxDeclNGen_4045_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 4, v_traceState_4046_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 5, v_cache_4047_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 6, v_messages_4048_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 7, v_infoState_4049_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 8, v_snapshotTasks_4050_);
                    v___x_4060_ = v_reuseFailAlloc_4063_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4061_ = lean_st_ref_set(v___y_4033_, v___x_4060_);
                v___x_4062_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4062_, 0, v_r_4054_);
                return v___x_4062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg___boxed(
    mut v___y_4068_: *mut LeanObject,
    mut v___y_4069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4070_: *mut LeanObject = core::ptr::null_mut();
    v_res_4070_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_4068_);
    lean_dec(v___y_4068_);
    return v_res_4070_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(
    mut v___y_4071_: *mut LeanObject,
    mut v___y_4072_: *mut LeanObject,
    mut v___y_4073_: *mut LeanObject,
    mut v___y_4074_: *mut LeanObject,
    mut v___y_4075_: *mut LeanObject,
    mut v___y_4076_: *mut LeanObject,
    mut v___y_4077_: *mut LeanObject,
    mut v___y_4078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    v___x_4080_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_4078_);
    return v___x_4080_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___boxed(
    mut v___y_4081_: *mut LeanObject,
    mut v___y_4082_: *mut LeanObject,
    mut v___y_4083_: *mut LeanObject,
    mut v___y_4084_: *mut LeanObject,
    mut v___y_4085_: *mut LeanObject,
    mut v___y_4086_: *mut LeanObject,
    mut v___y_4087_: *mut LeanObject,
    mut v___y_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4090_: *mut LeanObject = core::ptr::null_mut();
    v_res_4090_ =
        l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0(
            v___y_4081_,
            v___y_4082_,
            v___y_4083_,
            v___y_4084_,
            v___y_4085_,
            v___y_4086_,
            v___y_4087_,
            v___y_4088_,
        );
    lean_dec(v___y_4088_);
    lean_dec_ref(v___y_4087_);
    lean_dec(v___y_4086_);
    lean_dec_ref(v___y_4085_);
    lean_dec(v___y_4084_);
    lean_dec_ref(v___y_4083_);
    lean_dec(v___y_4082_);
    lean_dec_ref(v___y_4081_);
    return v_res_4090_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(
    mut v_e_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4094_: u8 = 0;
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut v_unused_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4094_ = l_Lean_Expr_hasMVar(v_e_4091_);
                if v___x_4094_ == 0 {
                    v___x_4095_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4095_, 0, v_e_4091_);
                    return v___x_4095_;
                } else {
                    v___x_4096_ = lean_st_ref_get(v___y_4092_);
                    v_mctx_4097_ = lean_ctor_get(v___x_4096_, 0);
                    lean_inc_ref(v_mctx_4097_);
                    lean_dec(v___x_4096_);
                    v___x_4098_ = l_Lean_instantiateMVarsCore(v_mctx_4097_, v_e_4091_);
                    v_fst_4099_ = lean_ctor_get(v___x_4098_, 0);
                    lean_inc(v_fst_4099_);
                    v_snd_4100_ = lean_ctor_get(v___x_4098_, 1);
                    lean_inc(v_snd_4100_);
                    lean_dec_ref(v___x_4098_);
                    v___x_4101_ = lean_st_ref_take(v___y_4092_);
                    v_cache_4102_ = lean_ctor_get(v___x_4101_, 1);
                    v_zetaDeltaFVarIds_4103_ = lean_ctor_get(v___x_4101_, 2);
                    v_postponed_4104_ = lean_ctor_get(v___x_4101_, 3);
                    v_diag_4105_ = lean_ctor_get(v___x_4101_, 4);
                    v_isSharedCheck_4114_ = (!lean_is_exclusive(v___x_4101_)) as u8;
                    if v_isSharedCheck_4114_ == 0 {
                        v_unused_4115_ = lean_ctor_get(v___x_4101_, 0);
                        lean_dec(v_unused_4115_);
                        v___x_4107_ = v___x_4101_;
                        v_isShared_4108_ = v_isSharedCheck_4114_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4105_);
                        lean_inc(v_postponed_4104_);
                        lean_inc(v_zetaDeltaFVarIds_4103_);
                        lean_inc(v_cache_4102_);
                        lean_dec(v___x_4101_);
                        v___x_4107_ = lean_box(0);
                        v_isShared_4108_ = v_isSharedCheck_4114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4108_ == 0 {
                    lean_ctor_set(v___x_4107_, 0, v_snd_4100_);
                    v___x_4110_ = v___x_4107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_snd_4100_);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_cache_4102_);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 2, v_zetaDeltaFVarIds_4103_);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 3, v_postponed_4104_);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 4, v_diag_4105_);
                    v___x_4110_ = v_reuseFailAlloc_4113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4111_ = lean_st_ref_set(v___y_4092_, v___x_4110_);
                v___x_4112_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4112_, 0, v_fst_4099_);
                return v___x_4112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg___boxed(
    mut v_e_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4119_: *mut LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_4116_, v___y_4117_);
    lean_dec(v___y_4117_);
    return v_res_4119_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(
    mut v_e_4120_: *mut LeanObject,
    mut v___y_4121_: *mut LeanObject,
    mut v___y_4122_: *mut LeanObject,
    mut v___y_4123_: *mut LeanObject,
    mut v___y_4124_: *mut LeanObject,
    mut v___y_4125_: *mut LeanObject,
    mut v___y_4126_: *mut LeanObject,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    v___x_4130_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_e_4120_, v___y_4126_);
    return v___x_4130_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___boxed(
    mut v_e_4131_: *mut LeanObject,
    mut v___y_4132_: *mut LeanObject,
    mut v___y_4133_: *mut LeanObject,
    mut v___y_4134_: *mut LeanObject,
    mut v___y_4135_: *mut LeanObject,
    mut v___y_4136_: *mut LeanObject,
    mut v___y_4137_: *mut LeanObject,
    mut v___y_4138_: *mut LeanObject,
    mut v___y_4139_: *mut LeanObject,
    mut v___y_4140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4141_: *mut LeanObject = core::ptr::null_mut();
    v_res_4141_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1(
            v_e_4131_,
            v___y_4132_,
            v___y_4133_,
            v___y_4134_,
            v___y_4135_,
            v___y_4136_,
            v___y_4137_,
            v___y_4138_,
            v___y_4139_,
        );
    lean_dec(v___y_4139_);
    lean_dec_ref(v___y_4138_);
    lean_dec(v___y_4137_);
    lean_dec_ref(v___y_4136_);
    lean_dec(v___y_4135_);
    lean_dec_ref(v___y_4134_);
    lean_dec(v___y_4133_);
    lean_dec_ref(v___y_4132_);
    return v_res_4141_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(
    mut v___x_4142_: *mut LeanObject,
    mut v___x_4143_: *mut LeanObject,
    mut v___x_4144_: *mut LeanObject,
    mut v___x_4145_: *mut LeanObject,
    mut v___x_4146_: *mut LeanObject,
    mut v_as_4147_: *mut LeanObject,
    mut v_sz_4148_: usize,
    mut v_i_4149_: usize,
    mut v_b_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
    mut v___y_4153_: *mut LeanObject,
    mut v___y_4154_: *mut LeanObject,
    mut v___y_4155_: *mut LeanObject,
    mut v___y_4156_: *mut LeanObject,
    mut v___y_4157_: *mut LeanObject,
    mut v___y_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: usize = 0;
    let mut v___x_4163_: usize = 0;
    let mut v___x_4165_: u8 = 0;
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4171_: u8 = 0;
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4193_: u8 = 0;
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4197_: u8 = 0;
    let mut v_val_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4203_: u8 = 0;
    let mut v___f_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4208_: u8 = 0;
    let mut v_a_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4212_: u8 = 0;
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4216_: u8 = 0;
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4165_ = lean_usize_dec_lt(v_i_4149_, v_sz_4148_);
                if v___x_4165_ == 0 {
                    lean_dec_ref(v___x_4146_);
                    lean_dec_ref(v___x_4145_);
                    lean_dec_ref(v___x_4144_);
                    lean_dec(v___x_4143_);
                    lean_dec(v___x_4142_);
                    v___x_4166_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4166_, 0, v_b_4150_);
                    return v___x_4166_;
                } else {
                    v_fst_4167_ = lean_ctor_get(v_b_4150_, 0);
                    v_snd_4168_ = lean_ctor_get(v_b_4150_, 1);
                    v_isSharedCheck_4222_ = (!lean_is_exclusive(v_b_4150_)) as u8;
                    if v_isSharedCheck_4222_ == 0 {
                        v___x_4170_ = v_b_4150_;
                        v_isShared_4171_ = v_isSharedCheck_4222_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_4168_);
                        lean_inc(v_fst_4167_);
                        lean_dec(v_b_4150_);
                        v___x_4170_ = lean_box(0);
                        v_isShared_4171_ = v_isSharedCheck_4222_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4162_ = 1usize;
                v___x_4163_ = lean_usize_add(v_i_4149_, v___x_4162_);
                v_i_4149_ = v___x_4163_;
                v_b_4150_ = v_a_4161_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4172_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0;
                v___x_4173_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                v___x_4174_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1;
                v_a_4175_ = lean_array_uget_borrowed(v_as_4147_, v_i_4149_);
                lean_inc(v_a_4175_);
                lean_inc(v_fst_4167_);
                lean_inc_ref(v___x_4145_);
                v___x_4217_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful(
                    v___x_4145_,
                    v_fst_4167_,
                    v_a_4175_,
                    v___y_4151_,
                    v___y_4152_,
                    v___y_4153_,
                    v___y_4154_,
                    v___y_4155_,
                    v___y_4156_,
                    v___y_4157_,
                    v___y_4158_,
                );
                if lean_obj_tag(v___x_4217_) == 0 {
                    v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
                    lean_inc(v_a_4218_);
                    if lean_obj_tag(v_a_4218_) == 0 {
                        lean_dec_ref_known(v___x_4217_, 1);
                        lean_inc(v_a_4175_);
                        lean_inc(v_fst_4167_);
                        lean_inc_ref(v___x_4145_);
                        v___x_4219_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure(
                            v___x_4145_,
                            v_fst_4167_,
                            v_a_4175_,
                            v___y_4151_,
                            v___y_4152_,
                            v___y_4153_,
                            v___y_4154_,
                            v___y_4155_,
                            v___y_4156_,
                            v___y_4157_,
                            v___y_4158_,
                        );
                        if lean_obj_tag(v___x_4219_) == 0 {
                            v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
                            lean_inc(v_a_4220_);
                            if lean_obj_tag(v_a_4220_) == 0 {
                                lean_dec_ref_known(v___x_4219_, 1);
                                lean_inc(v_a_4175_);
                                lean_inc(v_fst_4167_);
                                lean_inc_ref(v___x_4145_);
                                v___x_4221_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeForall(
                                    v___x_4145_,
                                    v_fst_4167_,
                                    v_a_4175_,
                                    v___y_4151_,
                                    v___y_4152_,
                                    v___y_4153_,
                                    v___y_4154_,
                                    v___y_4155_,
                                    v___y_4156_,
                                    v___y_4157_,
                                    v___y_4158_,
                                );
                                v___y_4177_ = v___x_4221_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec_ref_known(v_a_4220_, 1);
                                v___y_4177_ = v___x_4219_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___y_4177_ = v___x_4219_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_4218_, 1);
                        v___y_4177_ = v___x_4217_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_4177_ = v___x_4217_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v___y_4177_) == 0 {
                    v_a_4178_ = lean_ctor_get(v___y_4177_, 0);
                    lean_inc(v_a_4178_);
                    lean_dec_ref_known(v___y_4177_, 1);
                    if lean_obj_tag(v_a_4178_) == 0 {
                        v___x_4179_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___closed__1);
                        lean_inc(v_fst_4167_);
                        v___x_4180_ = l_Lean_MessageData_ofExpr(v_fst_4167_);
                        v___x_4181_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4181_, 0, v___x_4179_);
                        lean_ctor_set(v___x_4181_, 1, v___x_4180_);
                        v___x_4182_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__8);
                        v___x_4183_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4183_, 0, v___x_4181_);
                        lean_ctor_set(v___x_4183_, 1, v___x_4182_);
                        lean_inc(v_a_4175_);
                        v___x_4184_ = l_Lean_MessageData_ofSyntax(v_a_4175_);
                        v___x_4185_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4185_, 0, v___x_4183_);
                        lean_ctor_set(v___x_4185_, 1, v___x_4184_);
                        v___x_4186_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful_spec__0___redArg(v___x_4185_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
                        if lean_obj_tag(v___x_4186_) == 0 {
                            lean_dec_ref_known(v___x_4186_, 1);
                            if v_isShared_4171_ == 0 {
                                v___x_4188_ = v___x_4170_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_fst_4167_);
                                lean_ctor_set(v_reuseFailAlloc_4189_, 1, v_snd_4168_);
                                v___x_4188_ = v_reuseFailAlloc_4189_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4170_);
                            lean_dec(v_snd_4168_);
                            lean_dec(v_fst_4167_);
                            lean_dec_ref(v___x_4146_);
                            lean_dec_ref(v___x_4145_);
                            lean_dec_ref(v___x_4144_);
                            lean_dec(v___x_4143_);
                            lean_dec(v___x_4142_);
                            v_a_4190_ = lean_ctor_get(v___x_4186_, 0);
                            v_isSharedCheck_4197_ = (!lean_is_exclusive(v___x_4186_)) as u8;
                            if v_isSharedCheck_4197_ == 0 {
                                v___x_4192_ = v___x_4186_;
                                v_isShared_4193_ = v_isSharedCheck_4197_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4190_);
                                lean_dec(v___x_4186_);
                                v___x_4192_ = lean_box(0);
                                v_isShared_4193_ = v_isSharedCheck_4197_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4170_);
                        v_val_4198_ = lean_ctor_get(v_a_4178_, 0);
                        lean_inc(v_val_4198_);
                        lean_dec_ref_known(v_a_4178_, 1);
                        v_fst_4199_ = lean_ctor_get(v_val_4198_, 0);
                        v_snd_4200_ = lean_ctor_get(v_val_4198_, 1);
                        v_isSharedCheck_4208_ = (!lean_is_exclusive(v_val_4198_)) as u8;
                        if v_isSharedCheck_4208_ == 0 {
                            v___x_4202_ = v_val_4198_;
                            v_isShared_4203_ = v_isSharedCheck_4208_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_snd_4200_);
                            lean_inc(v_fst_4199_);
                            lean_dec(v_val_4198_);
                            v___x_4202_ = lean_box(0);
                            v_isShared_4203_ = v_isSharedCheck_4208_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4170_);
                    lean_dec(v_snd_4168_);
                    lean_dec(v_fst_4167_);
                    lean_dec_ref(v___x_4146_);
                    lean_dec_ref(v___x_4145_);
                    lean_dec_ref(v___x_4144_);
                    lean_dec(v___x_4143_);
                    lean_dec(v___x_4142_);
                    v_a_4209_ = lean_ctor_get(v___y_4177_, 0);
                    v_isSharedCheck_4216_ = (!lean_is_exclusive(v___y_4177_)) as u8;
                    if v_isSharedCheck_4216_ == 0 {
                        v___x_4211_ = v___y_4177_;
                        v_isShared_4212_ = v_isSharedCheck_4216_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4209_);
                        lean_dec(v___y_4177_);
                        v___x_4211_ = lean_box(0);
                        v_isShared_4212_ = v_isSharedCheck_4216_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v_a_4161_ = v___x_4188_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_4193_ == 0 {
                    v___x_4195_ = v___x_4192_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
                    v___x_4195_ = v_reuseFailAlloc_4196_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4195_;
            }
            7 => {
                lean_inc_ref(v___x_4146_);
                lean_inc(v_fst_4199_);
                lean_inc_ref(v___x_4145_);
                lean_inc_ref(v___x_4144_);
                lean_inc(v___x_4143_);
                lean_inc(v___x_4142_);
                v___f_4204_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__1___lam__0 as *mut core::ffi::c_void, 13, 12);
                lean_closure_set(v___f_4204_, 0, v___x_4172_);
                lean_closure_set(v___f_4204_, 1, v___x_4173_);
                lean_closure_set(v___f_4204_, 2, v___x_4174_);
                lean_closure_set(v___f_4204_, 3, v___x_4142_);
                lean_closure_set(v___f_4204_, 4, v___x_4143_);
                lean_closure_set(v___f_4204_, 5, v___x_4144_);
                lean_closure_set(v___f_4204_, 6, v___x_4145_);
                lean_closure_set(v___f_4204_, 7, v_fst_4167_);
                lean_closure_set(v___f_4204_, 8, v_fst_4199_);
                lean_closure_set(v___f_4204_, 9, v___x_4146_);
                lean_closure_set(v___f_4204_, 10, v_snd_4200_);
                lean_closure_set(v___f_4204_, 11, v_snd_4168_);
                if v_isShared_4203_ == 0 {
                    lean_ctor_set(v___x_4202_, 1, v___f_4204_);
                    v___x_4206_ = v___x_4202_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_fst_4199_);
                    lean_ctor_set(v_reuseFailAlloc_4207_, 1, v___f_4204_);
                    v___x_4206_ = v_reuseFailAlloc_4207_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_4161_ = v___x_4206_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_4212_ == 0 {
                    v___x_4214_ = v___x_4211_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
                    v___x_4214_ = v_reuseFailAlloc_4215_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4223_: *mut LeanObject = *_args.add(0);
    let mut v___x_4224_: *mut LeanObject = *_args.add(1);
    let mut v___x_4225_: *mut LeanObject = *_args.add(2);
    let mut v___x_4226_: *mut LeanObject = *_args.add(3);
    let mut v___x_4227_: *mut LeanObject = *_args.add(4);
    let mut v_as_4228_: *mut LeanObject = *_args.add(5);
    let mut v_sz_4229_: *mut LeanObject = *_args.add(6);
    let mut v_i_4230_: *mut LeanObject = *_args.add(7);
    let mut v_b_4231_: *mut LeanObject = *_args.add(8);
    let mut v___y_4232_: *mut LeanObject = *_args.add(9);
    let mut v___y_4233_: *mut LeanObject = *_args.add(10);
    let mut v___y_4234_: *mut LeanObject = *_args.add(11);
    let mut v___y_4235_: *mut LeanObject = *_args.add(12);
    let mut v___y_4236_: *mut LeanObject = *_args.add(13);
    let mut v___y_4237_: *mut LeanObject = *_args.add(14);
    let mut v___y_4238_: *mut LeanObject = *_args.add(15);
    let mut v___y_4239_: *mut LeanObject = *_args.add(16);
    let mut v___y_4240_: *mut LeanObject = *_args.add(17);
    let mut v_sz_boxed_4241_: usize = 0;
    let mut v_i_boxed_4242_: usize = 0;
    let mut v_res_4243_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4241_ = lean_unbox_usize(v_sz_4229_);
    lean_dec(v_sz_4229_);
    v_i_boxed_4242_ = lean_unbox_usize(v_i_4230_);
    lean_dec(v_i_4230_);
    v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_4223_, v___x_4224_, v___x_4225_, v___x_4226_, v___x_4227_, v_as_4228_, v_sz_boxed_4241_, v_i_boxed_4242_, v_b_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
    lean_dec(v___y_4239_);
    lean_dec_ref(v___y_4238_);
    lean_dec(v___y_4237_);
    lean_dec_ref(v___y_4236_);
    lean_dec(v___y_4235_);
    lean_dec_ref(v___y_4234_);
    lean_dec(v___y_4233_);
    lean_dec_ref(v___y_4232_);
    lean_dec_ref(v_as_4228_);
    return v_res_4243_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    v___x_4251_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__3;
    v___x_4252_ = lean_unsigned_to_nat(33);
    v___x_4253_ = lean_unsigned_to_nat(175);
    v___x_4254_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__2;
    v___x_4255_ = l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__15;
    v___x_4256_ = l_mkPanicMessageWithDecl(
        v___x_4255_,
        v___x_4254_,
        v___x_4253_,
        v___x_4252_,
        v___x_4251_,
    );
    return v___x_4256_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(
    mut v___x_4257_: *mut LeanObject,
    mut v___x_4258_: *mut LeanObject,
    mut v___x_4259_: u8,
    mut v_u_4260_: *mut LeanObject,
    mut v_00_u03c3s_4261_: *mut LeanObject,
    mut v___x_4262_: *mut LeanObject,
    mut v_hyp_4263_: *mut LeanObject,
    mut v_hyps_4264_: *mut LeanObject,
    mut v_target_4265_: *mut LeanObject,
    mut v_args_4266_: *mut LeanObject,
    mut v_fst_4267_: *mut LeanObject,
    mut v___y_4268_: *mut LeanObject,
    mut v___y_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
    mut v___y_4271_: *mut LeanObject,
    mut v___y_4272_: *mut LeanObject,
    mut v___y_4273_: *mut LeanObject,
    mut v___y_4274_: *mut LeanObject,
    mut v___y_4275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: u8 = 0;
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4314_: usize = 0;
    let mut v___x_4315_: usize = 0;
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4322_: u8 = 0;
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4341_: u8 = 0;
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4348_: u8 = 0;
    let mut v_a_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4352_: u8 = 0;
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4356_: u8 = 0;
    let mut v_a_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4360_: u8 = 0;
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4364_: u8 = 0;
    let mut v_a_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4368_: u8 = 0;
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v_a_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4376_: u8 = 0;
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4380_: u8 = 0;
    let mut v_a_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4384_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4277_ = l_Lean_Elab_Tactic_elabTerm(
                    v___x_4257_,
                    v___x_4258_,
                    v___x_4259_,
                    v___y_4268_,
                    v___y_4269_,
                    v___y_4270_,
                    v___y_4271_,
                    v___y_4272_,
                    v___y_4273_,
                    v___y_4274_,
                    v___y_4275_,
                );
                if lean_obj_tag(v___x_4277_) == 0 {
                    v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
                    lean_inc_n(v_a_4278_, 2);
                    lean_dec_ref_known(v___x_4277_, 1);
                    lean_inc(v___y_4275_);
                    lean_inc_ref(v___y_4274_);
                    lean_inc(v___y_4273_);
                    lean_inc_ref(v___y_4272_);
                    v___x_4279_ = lean_infer_type(
                        v_a_4278_,
                        v___y_4272_,
                        v___y_4273_,
                        v___y_4274_,
                        v___y_4275_,
                    );
                    if lean_obj_tag(v___x_4279_) == 0 {
                        v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
                        lean_inc(v_a_4280_);
                        lean_dec_ref_known(v___x_4279_, 1);
                        v___x_4281_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__0;
                        v___x_4282_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                        v___x_4283_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpStateful___closed__1;
                        v___x_4284_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__0;
                        v___x_4285_ = lean_box(0);
                        lean_inc(v_u_4260_);
                        v___x_4286_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4286_, 0, v_u_4260_);
                        lean_ctor_set(v___x_4286_, 1, v___x_4285_);
                        lean_inc_ref(v___x_4286_);
                        v___x_4287_ = l_Lean_mkConst(v___x_4284_, v___x_4286_);
                        lean_inc_ref(v_00_u03c3s_4261_);
                        v___x_4288_ = l_Lean_Expr_app___override(v___x_4287_, v_00_u03c3s_4261_);
                        v___x_4289_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4289_, 0, v___x_4288_);
                        v___x_4290_ = 0;
                        v___x_4291_ = lean_box(0);
                        v___x_4292_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_4289_,
                            v___x_4290_,
                            v___x_4291_,
                            v___y_4272_,
                            v___y_4273_,
                            v___y_4274_,
                            v___y_4275_,
                        );
                        if lean_obj_tag(v___x_4292_) == 0 {
                            v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
                            lean_inc_n(v_a_4293_, 2);
                            lean_dec_ref_known(v___x_4292_, 1);
                            v___x_4294_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_mSpecializeImpPure___closed__5;
                            lean_inc_ref(v___x_4262_);
                            v___x_4295_ = l_Lean_Name_mkStr5(
                                v___x_4281_,
                                v___x_4282_,
                                v___x_4283_,
                                v___x_4262_,
                                v___x_4294_,
                            );
                            lean_inc_ref(v___x_4286_);
                            v___x_4296_ = l_Lean_mkConst(v___x_4295_, v___x_4286_);
                            lean_inc_ref(v_00_u03c3s_4261_);
                            lean_inc(v_a_4280_);
                            v___x_4297_ =
                                l_Lean_mkApp3(v___x_4296_, v_a_4280_, v_00_u03c3s_4261_, v_a_4293_);
                            v___x_4298_ = lean_box(0);
                            v___x_4299_ = l_Lean_Meta_synthInstance(
                                v___x_4297_,
                                v___x_4298_,
                                v___y_4272_,
                                v___y_4273_,
                                v___y_4274_,
                                v___y_4275_,
                            );
                            if lean_obj_tag(v___x_4299_) == 0 {
                                v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
                                lean_inc(v_a_4300_);
                                lean_dec_ref_known(v___x_4299_, 1);
                                v___x_4301_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__0___redArg(v___y_4275_);
                                v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
                                lean_inc(v_a_4302_);
                                lean_dec_ref(v___x_4301_);
                                v___x_4303_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__1___redArg(v_a_4293_, v___y_4273_);
                                v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
                                lean_inc(v_a_4304_);
                                lean_dec_ref(v___x_4303_);
                                v___x_4305_ = l_Lean_TSyntax_getId(v_hyp_4263_);
                                v___x_4306_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v___x_4306_, 0, v___x_4305_);
                                lean_ctor_set(v___x_4306_, 1, v_a_4302_);
                                lean_ctor_set(v___x_4306_, 2, v_a_4304_);
                                v___x_4307_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_4306_);
                                v___x_4308_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                                v___x_4309_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__1;
                                v___x_4310_ = l_Lean_Name_mkStr6(
                                    v___x_4281_,
                                    v___x_4282_,
                                    v___x_4283_,
                                    v___x_4262_,
                                    v___x_4308_,
                                    v___x_4309_,
                                );
                                lean_inc_ref(v___x_4286_);
                                v___x_4311_ = l_Lean_mkConst(v___x_4310_, v___x_4286_);
                                lean_inc_ref_n(v_target_4265_, 2);
                                lean_inc_ref_n(v_hyps_4264_, 2);
                                lean_inc_ref(v___x_4307_);
                                lean_inc_ref_n(v_00_u03c3s_4261_, 2);
                                v___x_4312_ = lean_alloc_closure(
                                    l_Lean_mkApp8 as *mut core::ffi::c_void,
                                    9,
                                    8,
                                );
                                lean_closure_set(v___x_4312_, 0, v___x_4311_);
                                lean_closure_set(v___x_4312_, 1, v_00_u03c3s_4261_);
                                lean_closure_set(v___x_4312_, 2, v_a_4280_);
                                lean_closure_set(v___x_4312_, 3, v___x_4307_);
                                lean_closure_set(v___x_4312_, 4, v_hyps_4264_);
                                lean_closure_set(v___x_4312_, 5, v_target_4265_);
                                lean_closure_set(v___x_4312_, 6, v_a_4300_);
                                lean_closure_set(v___x_4312_, 7, v_a_4278_);
                                v___x_4313_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_4313_, 0, v___x_4307_);
                                lean_ctor_set(v___x_4313_, 1, v___x_4312_);
                                v_sz_4314_ = lean_array_size(v_args_4266_);
                                v___x_4315_ = 0usize;
                                lean_inc(v_u_4260_);
                                v___x_4316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure_spec__2(v___x_4286_, v_u_4260_, v_00_u03c3s_4261_, v_hyps_4264_, v_target_4265_, v_args_4266_, v_sz_4314_, v___x_4315_, v___x_4313_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
                                if lean_obj_tag(v___x_4316_) == 0 {
                                    v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
                                    lean_inc(v_a_4317_);
                                    lean_dec_ref_known(v___x_4316_, 1);
                                    v_fst_4318_ = lean_ctor_get(v_a_4317_, 0);
                                    v_snd_4319_ = lean_ctor_get(v_a_4317_, 1);
                                    v_isSharedCheck_4348_ = (!lean_is_exclusive(v_a_4317_)) as u8;
                                    if v_isSharedCheck_4348_ == 0 {
                                        v___x_4321_ = v_a_4317_;
                                        v_isShared_4322_ = v_isSharedCheck_4348_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_snd_4319_);
                                        lean_inc(v_fst_4318_);
                                        lean_dec(v_a_4317_);
                                        v___x_4321_ = lean_box(0);
                                        v_isShared_4322_ = v_isSharedCheck_4348_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___y_4275_);
                                    lean_dec_ref(v___y_4274_);
                                    lean_dec(v___y_4273_);
                                    lean_dec_ref(v___y_4272_);
                                    lean_dec(v_fst_4267_);
                                    lean_dec_ref(v_target_4265_);
                                    lean_dec_ref(v_hyps_4264_);
                                    lean_dec(v_hyp_4263_);
                                    lean_dec_ref(v_00_u03c3s_4261_);
                                    lean_dec(v_u_4260_);
                                    v_a_4349_ = lean_ctor_get(v___x_4316_, 0);
                                    v_isSharedCheck_4356_ = (!lean_is_exclusive(v___x_4316_)) as u8;
                                    if v_isSharedCheck_4356_ == 0 {
                                        v___x_4351_ = v___x_4316_;
                                        v_isShared_4352_ = v_isSharedCheck_4356_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4349_);
                                        lean_dec(v___x_4316_);
                                        v___x_4351_ = lean_box(0);
                                        v_isShared_4352_ = v_isSharedCheck_4356_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4293_);
                                lean_dec_ref_known(v___x_4286_, 2);
                                lean_dec(v_a_4280_);
                                lean_dec(v_a_4278_);
                                lean_dec(v___y_4275_);
                                lean_dec_ref(v___y_4274_);
                                lean_dec(v___y_4273_);
                                lean_dec_ref(v___y_4272_);
                                lean_dec(v_fst_4267_);
                                lean_dec_ref(v_target_4265_);
                                lean_dec_ref(v_hyps_4264_);
                                lean_dec(v_hyp_4263_);
                                lean_dec_ref(v___x_4262_);
                                lean_dec_ref(v_00_u03c3s_4261_);
                                lean_dec(v_u_4260_);
                                v_a_4357_ = lean_ctor_get(v___x_4299_, 0);
                                v_isSharedCheck_4364_ = (!lean_is_exclusive(v___x_4299_)) as u8;
                                if v_isSharedCheck_4364_ == 0 {
                                    v___x_4359_ = v___x_4299_;
                                    v_isShared_4360_ = v_isSharedCheck_4364_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4357_);
                                    lean_dec(v___x_4299_);
                                    v___x_4359_ = lean_box(0);
                                    v_isShared_4360_ = v_isSharedCheck_4364_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v___x_4286_, 2);
                            lean_dec(v_a_4280_);
                            lean_dec(v_a_4278_);
                            lean_dec(v___y_4275_);
                            lean_dec_ref(v___y_4274_);
                            lean_dec(v___y_4273_);
                            lean_dec_ref(v___y_4272_);
                            lean_dec(v_fst_4267_);
                            lean_dec_ref(v_target_4265_);
                            lean_dec_ref(v_hyps_4264_);
                            lean_dec(v_hyp_4263_);
                            lean_dec_ref(v___x_4262_);
                            lean_dec_ref(v_00_u03c3s_4261_);
                            lean_dec(v_u_4260_);
                            v_a_4365_ = lean_ctor_get(v___x_4292_, 0);
                            v_isSharedCheck_4372_ = (!lean_is_exclusive(v___x_4292_)) as u8;
                            if v_isSharedCheck_4372_ == 0 {
                                v___x_4367_ = v___x_4292_;
                                v_isShared_4368_ = v_isSharedCheck_4372_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_4365_);
                                lean_dec(v___x_4292_);
                                v___x_4367_ = lean_box(0);
                                v_isShared_4368_ = v_isSharedCheck_4372_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4278_);
                        lean_dec(v___y_4275_);
                        lean_dec_ref(v___y_4274_);
                        lean_dec(v___y_4273_);
                        lean_dec_ref(v___y_4272_);
                        lean_dec(v_fst_4267_);
                        lean_dec_ref(v_target_4265_);
                        lean_dec_ref(v_hyps_4264_);
                        lean_dec(v_hyp_4263_);
                        lean_dec_ref(v___x_4262_);
                        lean_dec_ref(v_00_u03c3s_4261_);
                        lean_dec(v_u_4260_);
                        v_a_4373_ = lean_ctor_get(v___x_4279_, 0);
                        v_isSharedCheck_4380_ = (!lean_is_exclusive(v___x_4279_)) as u8;
                        if v_isSharedCheck_4380_ == 0 {
                            v___x_4375_ = v___x_4279_;
                            v_isShared_4376_ = v_isSharedCheck_4380_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_4373_);
                            lean_dec(v___x_4279_);
                            v___x_4375_ = lean_box(0);
                            v_isShared_4376_ = v_isSharedCheck_4380_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_4275_);
                    lean_dec_ref(v___y_4274_);
                    lean_dec(v___y_4273_);
                    lean_dec_ref(v___y_4272_);
                    lean_dec(v_fst_4267_);
                    lean_dec_ref(v_target_4265_);
                    lean_dec_ref(v_hyps_4264_);
                    lean_dec(v_hyp_4263_);
                    lean_dec_ref(v___x_4262_);
                    lean_dec_ref(v_00_u03c3s_4261_);
                    lean_dec(v_u_4260_);
                    v_a_4381_ = lean_ctor_get(v___x_4277_, 0);
                    v_isSharedCheck_4388_ = (!lean_is_exclusive(v___x_4277_)) as u8;
                    if v_isSharedCheck_4388_ == 0 {
                        v___x_4383_ = v___x_4277_;
                        v_isShared_4384_ = v_isSharedCheck_4388_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4381_);
                        lean_dec(v___x_4277_);
                        v___x_4383_ = lean_box(0);
                        v_isShared_4384_ = v_isSharedCheck_4388_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_fst_4318_);
                v___x_4323_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_fst_4318_);
                if lean_obj_tag(v___x_4323_) == 1 {
                    v_val_4324_ = lean_ctor_get(v___x_4323_, 0);
                    lean_inc(v_val_4324_);
                    lean_dec_ref_known(v___x_4323_, 1);
                    lean_inc_ref(v_00_u03c3s_4261_);
                    v___x_4325_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                        v_hyp_4263_,
                        v_00_u03c3s_4261_,
                        v_val_4324_,
                        v___x_4259_,
                        v___y_4272_,
                        v___y_4273_,
                        v___y_4274_,
                        v___y_4275_,
                    );
                    if lean_obj_tag(v___x_4325_) == 0 {
                        lean_dec_ref_known(v___x_4325_, 1);
                        lean_inc_ref(v_00_u03c3s_4261_);
                        lean_inc(v_u_4260_);
                        v___x_4326_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                            v_u_4260_,
                            v_00_u03c3s_4261_,
                            v_hyps_4264_,
                            v_fst_4318_,
                        );
                        v___x_4327_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v___x_4327_, 0, v_u_4260_);
                        lean_ctor_set(v___x_4327_, 1, v_00_u03c3s_4261_);
                        lean_ctor_set(v___x_4327_, 2, v___x_4326_);
                        lean_ctor_set(v___x_4327_, 3, v_target_4265_);
                        v___x_4328_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_4327_);
                        v___x_4329_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v___x_4328_,
                            v___x_4291_,
                            v___y_4272_,
                            v___y_4273_,
                            v___y_4274_,
                            v___y_4275_,
                        );
                        if lean_obj_tag(v___x_4329_) == 0 {
                            v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
                            lean_inc_n(v_a_4330_, 2);
                            lean_dec_ref_known(v___x_4329_, 1);
                            v___x_4331_ = lean_apply_1(v_snd_4319_, v_a_4330_);
                            v___x_4332_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__2___redArg(v_fst_4267_, v___x_4331_, v___y_4273_);
                            lean_dec_ref(v___x_4332_);
                            v___x_4333_ = l_Lean_Expr_mvarId_x21(v_a_4330_);
                            lean_dec(v_a_4330_);
                            if v_isShared_4322_ == 0 {
                                lean_ctor_set_tag(v___x_4321_, 1);
                                lean_ctor_set(v___x_4321_, 1, v___x_4285_);
                                lean_ctor_set(v___x_4321_, 0, v___x_4333_);
                                v___x_4335_ = v___x_4321_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4333_);
                                lean_ctor_set(v_reuseFailAlloc_4337_, 1, v___x_4285_);
                                v___x_4335_ = v_reuseFailAlloc_4337_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4321_);
                            lean_dec(v_snd_4319_);
                            lean_dec(v___y_4275_);
                            lean_dec_ref(v___y_4274_);
                            lean_dec(v___y_4273_);
                            lean_dec_ref(v___y_4272_);
                            lean_dec(v_fst_4267_);
                            v_a_4338_ = lean_ctor_get(v___x_4329_, 0);
                            v_isSharedCheck_4345_ = (!lean_is_exclusive(v___x_4329_)) as u8;
                            if v_isSharedCheck_4345_ == 0 {
                                v___x_4340_ = v___x_4329_;
                                v_isShared_4341_ = v_isSharedCheck_4345_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4338_);
                                lean_dec(v___x_4329_);
                                v___x_4340_ = lean_box(0);
                                v_isShared_4341_ = v_isSharedCheck_4345_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4321_);
                        lean_dec(v_snd_4319_);
                        lean_dec(v_fst_4318_);
                        lean_dec(v___y_4275_);
                        lean_dec_ref(v___y_4274_);
                        lean_dec(v___y_4273_);
                        lean_dec_ref(v___y_4272_);
                        lean_dec(v_fst_4267_);
                        lean_dec_ref(v_target_4265_);
                        lean_dec_ref(v_hyps_4264_);
                        lean_dec_ref(v_00_u03c3s_4261_);
                        lean_dec(v_u_4260_);
                        return v___x_4325_;
                    }
                } else {
                    lean_dec(v___x_4323_);
                    lean_del_object(v___x_4321_);
                    lean_dec(v_snd_4319_);
                    lean_dec(v_fst_4318_);
                    lean_dec(v_fst_4267_);
                    lean_dec_ref(v_target_4265_);
                    lean_dec_ref(v_hyps_4264_);
                    lean_dec(v_hyp_4263_);
                    lean_dec_ref(v_00_u03c3s_4261_);
                    lean_dec(v_u_4260_);
                    v___x_4346_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___closed__4);
                    v___x_4347_ =
                        l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__3(
                            v___x_4346_,
                            v___y_4268_,
                            v___y_4269_,
                            v___y_4270_,
                            v___y_4271_,
                            v___y_4272_,
                            v___y_4273_,
                            v___y_4274_,
                            v___y_4275_,
                        );
                    lean_dec(v___y_4275_);
                    lean_dec_ref(v___y_4274_);
                    lean_dec(v___y_4273_);
                    lean_dec_ref(v___y_4272_);
                    return v___x_4347_;
                }
            }
            2 => {
                v___x_4336_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_4335_,
                    v___y_4269_,
                    v___y_4272_,
                    v___y_4273_,
                    v___y_4274_,
                    v___y_4275_,
                );
                lean_dec(v___y_4275_);
                lean_dec_ref(v___y_4274_);
                lean_dec(v___y_4273_);
                lean_dec_ref(v___y_4272_);
                return v___x_4336_;
            }
            3 => {
                if v_isShared_4341_ == 0 {
                    v___x_4343_ = v___x_4340_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
                    v___x_4343_ = v_reuseFailAlloc_4344_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4343_;
            }
            5 => {
                if v_isShared_4352_ == 0 {
                    v___x_4354_ = v___x_4351_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
                    v___x_4354_ = v_reuseFailAlloc_4355_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4354_;
            }
            7 => {
                if v_isShared_4360_ == 0 {
                    v___x_4362_ = v___x_4359_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
                    v___x_4362_ = v_reuseFailAlloc_4363_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4362_;
            }
            9 => {
                if v_isShared_4368_ == 0 {
                    v___x_4370_ = v___x_4367_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
                    v___x_4370_ = v_reuseFailAlloc_4371_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4370_;
            }
            11 => {
                if v_isShared_4376_ == 0 {
                    v___x_4378_ = v___x_4375_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
                    v___x_4378_ = v_reuseFailAlloc_4379_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4378_;
            }
            13 => {
                if v_isShared_4384_ == 0 {
                    v___x_4386_ = v___x_4383_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
                    v___x_4386_ = v_reuseFailAlloc_4387_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4389_: *mut LeanObject = *_args.add(0);
    let mut v___x_4390_: *mut LeanObject = *_args.add(1);
    let mut v___x_4391_: *mut LeanObject = *_args.add(2);
    let mut v_u_4392_: *mut LeanObject = *_args.add(3);
    let mut v_00_u03c3s_4393_: *mut LeanObject = *_args.add(4);
    let mut v___x_4394_: *mut LeanObject = *_args.add(5);
    let mut v_hyp_4395_: *mut LeanObject = *_args.add(6);
    let mut v_hyps_4396_: *mut LeanObject = *_args.add(7);
    let mut v_target_4397_: *mut LeanObject = *_args.add(8);
    let mut v_args_4398_: *mut LeanObject = *_args.add(9);
    let mut v_fst_4399_: *mut LeanObject = *_args.add(10);
    let mut v___y_4400_: *mut LeanObject = *_args.add(11);
    let mut v___y_4401_: *mut LeanObject = *_args.add(12);
    let mut v___y_4402_: *mut LeanObject = *_args.add(13);
    let mut v___y_4403_: *mut LeanObject = *_args.add(14);
    let mut v___y_4404_: *mut LeanObject = *_args.add(15);
    let mut v___y_4405_: *mut LeanObject = *_args.add(16);
    let mut v___y_4406_: *mut LeanObject = *_args.add(17);
    let mut v___y_4407_: *mut LeanObject = *_args.add(18);
    let mut v___y_4408_: *mut LeanObject = *_args.add(19);
    let mut v___x_10844__boxed_4409_: u8 = 0;
    let mut v_res_4410_: *mut LeanObject = core::ptr::null_mut();
    v___x_10844__boxed_4409_ = (lean_unbox(v___x_4391_) as u8);
    v_res_4410_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0(
        v___x_4389_,
        v___x_4390_,
        v___x_10844__boxed_4409_,
        v_u_4392_,
        v_00_u03c3s_4393_,
        v___x_4394_,
        v_hyp_4395_,
        v_hyps_4396_,
        v_target_4397_,
        v_args_4398_,
        v_fst_4399_,
        v___y_4400_,
        v___y_4401_,
        v___y_4402_,
        v___y_4403_,
        v___y_4404_,
        v___y_4405_,
        v___y_4406_,
        v___y_4407_,
    );
    lean_dec(v___y_4403_);
    lean_dec_ref(v___y_4402_);
    lean_dec(v___y_4401_);
    lean_dec_ref(v___y_4400_);
    lean_dec_ref(v_args_4398_);
    return v_res_4410_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(
    mut v_x_4424_: *mut LeanObject,
    mut v_a_4425_: *mut LeanObject,
    mut v_a_4426_: *mut LeanObject,
    mut v_a_4427_: *mut LeanObject,
    mut v_a_4428_: *mut LeanObject,
    mut v_a_4429_: *mut LeanObject,
    mut v_a_4430_: *mut LeanObject,
    mut v_a_4431_: *mut LeanObject,
    mut v_a_4432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: u8 = 0;
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: u8 = 0;
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: u8 = 0;
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyp_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: u8 = 0;
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4469_: u8 = 0;
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4434_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_;
                v___x_4435_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1;
                lean_inc(v_x_4424_);
                v___x_4436_ = l_Lean_Syntax_isOfKind(v_x_4424_, v___x_4435_);
                if v___x_4436_ == 0 {
                    lean_dec(v_x_4424_);
                    v___x_4437_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
                    return v___x_4437_;
                } else {
                    v___x_4438_ = lean_unsigned_to_nat(1);
                    v___x_4439_ = l_Lean_Syntax_getArg(v_x_4424_, v___x_4438_);
                    v___x_4440_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__4;
                    lean_inc(v___x_4439_);
                    v___x_4441_ = l_Lean_Syntax_isOfKind(v___x_4439_, v___x_4440_);
                    if v___x_4441_ == 0 {
                        lean_dec(v___x_4439_);
                        lean_dec(v_x_4424_);
                        v___x_4442_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
                        return v___x_4442_;
                    } else {
                        v___x_4443_ = lean_unsigned_to_nat(0);
                        v___x_4444_ = lean_unsigned_to_nat(2);
                        v___x_4445_ = l_Lean_Syntax_getArg(v_x_4424_, v___x_4444_);
                        v___x_4446_ = l_Lean_Syntax_matchesNull(v___x_4445_, v___x_4443_);
                        if v___x_4446_ == 0 {
                            lean_dec(v___x_4439_);
                            lean_dec(v_x_4424_);
                            v___x_4447_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__0___redArg();
                            return v___x_4447_;
                        } else {
                            v___x_4448_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                                v_a_4426_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_,
                            );
                            if lean_obj_tag(v___x_4448_) == 0 {
                                v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
                                lean_inc(v_a_4449_);
                                lean_dec_ref_known(v___x_4448_, 1);
                                v_snd_4450_ = lean_ctor_get(v_a_4449_, 1);
                                lean_inc(v_snd_4450_);
                                v_fst_4451_ = lean_ctor_get(v_a_4449_, 0);
                                lean_inc_n(v_fst_4451_, 2);
                                lean_dec(v_a_4449_);
                                v_u_4452_ = lean_ctor_get(v_snd_4450_, 0);
                                lean_inc(v_u_4452_);
                                v_00_u03c3s_4453_ = lean_ctor_get(v_snd_4450_, 1);
                                lean_inc_ref(v_00_u03c3s_4453_);
                                v_hyps_4454_ = lean_ctor_get(v_snd_4450_, 2);
                                lean_inc_ref(v_hyps_4454_);
                                v_target_4455_ = lean_ctor_get(v_snd_4450_, 3);
                                lean_inc_ref(v_target_4455_);
                                lean_dec(v_snd_4450_);
                                v___x_4456_ = l_Lean_Syntax_getArg(v___x_4439_, v___x_4443_);
                                v___x_4457_ = l_Lean_Syntax_getArg(v___x_4439_, v___x_4438_);
                                lean_dec(v___x_4439_);
                                v___x_4458_ = lean_unsigned_to_nat(4);
                                v_hyp_4459_ = l_Lean_Syntax_getArg(v_x_4424_, v___x_4458_);
                                lean_dec(v_x_4424_);
                                v_args_4460_ = l_Lean_Syntax_getArgs(v___x_4457_);
                                lean_dec(v___x_4457_);
                                v___x_4461_ = lean_box(0);
                                v___x_4462_ = 0;
                                v___x_4463_ = lean_box((v___x_4462_) as usize);
                                v___f_4464_ = lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___lam__0___boxed as *mut core::ffi::c_void, 20, 11);
                                lean_closure_set(v___f_4464_, 0, v___x_4456_);
                                lean_closure_set(v___f_4464_, 1, v___x_4461_);
                                lean_closure_set(v___f_4464_, 2, v___x_4463_);
                                lean_closure_set(v___f_4464_, 3, v_u_4452_);
                                lean_closure_set(v___f_4464_, 4, v_00_u03c3s_4453_);
                                lean_closure_set(v___f_4464_, 5, v___x_4434_);
                                lean_closure_set(v___f_4464_, 6, v_hyp_4459_);
                                lean_closure_set(v___f_4464_, 7, v_hyps_4454_);
                                lean_closure_set(v___f_4464_, 8, v_target_4455_);
                                lean_closure_set(v___f_4464_, 9, v_args_4460_);
                                lean_closure_set(v___f_4464_, 10, v_fst_4451_);
                                v___x_4465_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize_spec__4___redArg(v_fst_4451_, v___f_4464_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_);
                                return v___x_4465_;
                            } else {
                                lean_dec(v___x_4439_);
                                lean_dec(v_x_4424_);
                                v_a_4466_ = lean_ctor_get(v___x_4448_, 0);
                                v_isSharedCheck_4473_ = (!lean_is_exclusive(v___x_4448_)) as u8;
                                if v_isSharedCheck_4473_ == 0 {
                                    v___x_4468_ = v___x_4448_;
                                    v_isShared_4469_ = v_isSharedCheck_4473_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4466_);
                                    lean_dec(v___x_4448_);
                                    v___x_4468_ = lean_box(0);
                                    v_isShared_4469_ = v_isSharedCheck_4473_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4469_ == 0 {
                    v___x_4471_ = v___x_4468_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
                    v___x_4471_ = v_reuseFailAlloc_4472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed(
    mut v_x_4474_: *mut LeanObject,
    mut v_a_4475_: *mut LeanObject,
    mut v_a_4476_: *mut LeanObject,
    mut v_a_4477_: *mut LeanObject,
    mut v_a_4478_: *mut LeanObject,
    mut v_a_4479_: *mut LeanObject,
    mut v_a_4480_: *mut LeanObject,
    mut v_a_4481_: *mut LeanObject,
    mut v_a_4482_: *mut LeanObject,
    mut v_a_4483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4484_: *mut LeanObject = core::ptr::null_mut();
    v_res_4484_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure(
        v_x_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_,
        v_a_4482_,
    );
    lean_dec(v_a_4482_);
    lean_dec_ref(v_a_4481_);
    lean_dec(v_a_4480_);
    lean_dec_ref(v_a_4479_);
    lean_dec(v_a_4478_);
    lean_dec_ref(v_a_4477_);
    lean_dec(v_a_4476_);
    lean_dec_ref(v_a_4475_);
    return v_res_4484_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1()
-> *mut LeanObject {
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    v___x_4494_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4495_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___closed__1;
    v___x_4496_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___closed__1;
    v___x_4497_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4498_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4494_,
        v___x_4495_,
        v___x_4496_,
        v___x_4497_,
    );
    return v___x_4498_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1___boxed(
    mut v_a_4499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4500_: *mut LeanObject = core::ptr::null_mut();
    v_res_4500_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
    return v_res_4500_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Specialize_1458348229____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMSpecialize__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Specialize_0__Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMspecializePure__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(builtin);
}

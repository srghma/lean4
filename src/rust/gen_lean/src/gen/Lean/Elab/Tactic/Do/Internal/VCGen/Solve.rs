// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Solve
// Imports: Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache Lean.Elab.Tactic.Do.Internal.VCGen.Entails Lean.Meta.Sym.InstantiateS
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{l_Array_extract___redArg, l_Lean_Name_append};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Context::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Entails::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Reduce::l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f;
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::RuleCache::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::SpecDB::l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs;
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Util::{
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Do::VCGen::Basic::l_Lean_Elab_Tactic_Do_isJP;
use crate::r#gen::Lean::Elab::Tactic::Do::VCGen::Split::l_Lean_Elab_Tactic_Do_getSplitInfo_x3f;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_betaRev, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_fvarId_x3f, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isApp, l_Lean_Expr_isAppOf, l_Lean_Expr_isConst,
    l_Lean_Expr_isConstOf, l_Lean_Expr_isFVar, l_Lean_Expr_isForall, l_Lean_Expr_isLambda,
    l_Lean_Expr_isLet, l_Lean_Expr_letBody_x21, l_Lean_Expr_letE___override,
    l_Lean_Expr_letName_x21, l_Lean_Expr_letValue_x21, l_Lean_Expr_sort___override,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr,
    l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_FVarId_getUserName___redArg, l_Lean_FVarId_getValue_x3f___redArg,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    l_Lean_Meta_Sym_Internal_Sym_assertShared, l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
};
use crate::r#gen::Lean::Meta::Sym::InstantiateS::{
    initialize_Lean_Meta_Sym_InstantiateS, l_Lean_Meta_Sym_instantiateRevBetaS___redArg,
    runtime_initialize_Lean_Meta_Sym_InstantiateS,
};
use crate::r#gen::Lean::Meta::Sym::Pattern::l_Lean_Meta_Sym_isDefEqS;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommonInc___redArg;
use crate::r#gen::Lean::Meta::Tactic::Replace::l_Lean_MVarId_replaceTargetDefEq;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_reduceRecMatcher_x3f;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::ffi::lean_mk_array;
use crate::ffi::{lean_array_fset, lean_array_set};
use crate::ffi::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_infer_type;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [102, 111, 114, 97, 108, 108, 115, 32, 105, 110, 32, 96, 115, 111, 108, 118, 101, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 116, 45, 105, 110, 116, 114, 111, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [118, 99, 103, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2_value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3_value) as *mut crate::leanh::LeanObject,17186385980065365684 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut crate::leanh::LeanObject,6272605754531080404 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5_value) as *mut crate::leanh::LeanObject,15978311213600074545 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [108, 101, 116, 45, 122, 101, 116, 97, 45, 100, 117, 112, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12_value: crate::leanh::LeanStringObject<104> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 104, m_capacity: 104, m_length: 103, m_data: [109, 118, 99, 103, 101, 110, 39, 58, 32, 115, 104, 97, 114, 101, 100, 45, 99, 111, 110, 116, 105, 110, 117, 97, 116, 105, 111, 110, 32, 104, 97, 110, 100, 108, 105, 110, 103, 32, 102, 111, 114, 32, 96, 95, 95, 100, 111, 95, 106, 112, 96, 32, 105, 115, 32, 110, 111, 116, 32, 121, 101, 116, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 46, 32, 68, 101, 116, 101, 99, 116, 105, 111, 110, 32, 112, 111, 105, 110, 116, 32, 114, 101, 97, 99, 104, 101, 100, 32, 97, 116, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14_value: crate::leanh::LeanStringObject<205> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 205, m_capacity: 205, m_length: 204, m_data: [59, 32, 116, 104, 101, 32, 117, 112, 115, 116, 114, 101, 97, 109, 32, 96, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 111, 110, 74, 111, 105, 110, 80, 111, 105, 110, 116, 96, 32, 40, 96, 115, 114, 99, 47, 76, 101, 97, 110, 47, 69, 108, 97, 98, 47, 84, 97, 99, 116, 105, 99, 47, 68, 111, 47, 86, 67, 71, 101, 110, 46, 108, 101, 97, 110, 58, 50, 49, 53, 96, 41, 32, 110, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 32, 112, 111, 114, 116, 101, 100, 32, 116, 111, 32, 116, 104, 101, 32, 119, 111, 114, 107, 108, 105, 115, 116, 32, 115, 116, 121, 108, 101, 46, 32, 68, 114, 111, 112, 32, 96, 40, 106, 112, 32, 58, 61, 32, 116, 114, 117, 101, 41, 96, 32, 116, 111, 32, 102, 97, 108, 108, 32, 98, 97, 99, 107, 32, 116, 111, 32, 116, 104, 101, 32, 100, 101, 102, 97, 117, 108, 116, 32, 122, 101, 116, 97, 45, 117, 110, 102, 111, 108, 100, 32, 98, 101, 104, 97, 118, 105, 111, 117, 114, 46, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1_value) as *mut crate::leanh::LeanObject,11963640885769744415 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [65, 112, 112, 108, 121, 105, 110, 103, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 80, 114, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 110, 116, 97, 105, 108, 115, 95, 99, 111, 110, 115, 95, 105, 110, 116, 114, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value) as *mut crate::leanh::LeanObject,13332341187416043682 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3_value) as *mut crate::leanh::LeanObject,16895493190937329785 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 116, 111, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [32, 102, 97, 105, 108, 101, 100, 46, 32, 73, 116, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 46, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 110, 116, 97, 105, 108, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 101, 102, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value) as *mut crate::leanh::LeanObject,13332341187416043682 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__0_value) as *mut crate::leanh::LeanObject,515334035361346902 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__1_value) as *mut crate::leanh::LeanObject,1565800902179044421 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__3_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [83, 111, 108, 118, 101, 100, 32, 98, 121, 32, 114, 102, 108, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__5_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 114, 121, 105, 110, 103, 32, 114, 102, 108, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 116, 45, 104, 111, 105, 115, 116, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0: u64 = 0;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 112, 108, 105, 116, 32, 114, 117, 108, 101, 32, 102, 111, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 115, 112, 108, 105, 116, 32, 114, 117, 108, 101, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [102, 118, 97, 114, 45, 122, 101, 116, 97, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 112, 101, 99, 32, 114, 117, 108, 101, 32, 102, 111, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 114, 117, 108, 101, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [78, 101, 101, 100, 101, 100, 32, 115, 116, 97, 116, 101, 32, 105, 110, 116, 114, 111, 46, 32, 82, 101, 116, 114, 121, 105, 110, 103, 46, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [82, 117, 108, 101, 32, 116, 121, 112, 101, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [83, 112, 101, 99, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 103, 108, 111, 98, 97, 108, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 108, 111, 99, 97, 108, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 115, 116, 120, 32, 95, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed as *const core::ffi::c_void, m_arity: 14, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [65, 112, 112, 108, 121, 105, 110, 103, 32, 97, 32, 115, 112, 101, 99, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [46, 32, 69, 120, 99, 101, 115, 115, 32, 97, 114, 103, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value) as *mut crate::leanh::LeanObject,13332341187416043682 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__0_value) as *mut crate::leanh::LeanObject,515334035361346902 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [80, 114, 101, 100, 84, 114, 97, 110, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [97, 112, 112, 108, 121, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        14660636995802757424 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        11849051038469469124 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [87, 80, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [119, 112, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_value)
            as *mut crate::leanh::LeanObject,
        6757038018435374033 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17511313520436183663 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 11,
    m_data: [
        240, 159, 147, 156, 32, 80, 114, 111, 103, 114, 97, 109, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 10,
    m_data: [
        240, 159, 142, 175, 32, 84, 97, 114, 103, 101, 116, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx(
    mut v_x_3418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3418_) {
        0 => {
            let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3419_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3419_;
        }
        1 => {
            let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3420_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3420_;
        }
        2 => {
            let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3421_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3421_;
        }
        3 => {
            let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3422_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_3422_;
        }
        _ => {
            let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3423_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_3423_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx___boxed(
    mut v_x_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx(v_x_3424_);
    crate::leanh::lean_dec_ref(v_x_3424_);
    return v_res_3425_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
    mut v_t_3426_: *mut crate::leanh::LeanObject,
    mut v_k_3427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_3426_) {
        3 => {
            let mut v_e_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_monad_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_thms_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_e_3428_ = crate::leanh::lean_ctor_get(v_t_3426_, 0);
            crate::leanh::lean_inc_ref(v_e_3428_);
            v_monad_3429_ = crate::leanh::lean_ctor_get(v_t_3426_, 1);
            crate::leanh::lean_inc_ref(v_monad_3429_);
            v_thms_3430_ = crate::leanh::lean_ctor_get(v_t_3426_, 2);
            crate::leanh::lean_inc_ref(v_thms_3430_);
            crate::leanh::lean_dec_ref_known(v_t_3426_, 3);
            v___x_3431_ =
                crate::leanh::lean_apply_3(v_k_3427_, v_e_3428_, v_monad_3429_, v_thms_3430_);
            return v___x_3431_;
        }
        4 => {
            let mut v_scope_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_subgoals_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_scope_3432_ = crate::leanh::lean_ctor_get(v_t_3426_, 0);
            crate::leanh::lean_inc_ref(v_scope_3432_);
            v_subgoals_3433_ = crate::leanh::lean_ctor_get(v_t_3426_, 1);
            crate::leanh::lean_inc(v_subgoals_3433_);
            crate::leanh::lean_dec_ref_known(v_t_3426_, 2);
            v___x_3434_ = crate::leanh::lean_apply_2(v_k_3427_, v_scope_3432_, v_subgoals_3433_);
            return v___x_3434_;
        }
        _ => {
            let mut v_target_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_target_3435_ = crate::leanh::lean_ctor_get(v_t_3426_, 0);
            crate::leanh::lean_inc_ref(v_target_3435_);
            crate::leanh::lean_dec_ref(v_t_3426_);
            v___x_3436_ = crate::leanh::lean_apply_1(v_k_3427_, v_target_3435_);
            return v___x_3436_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim(
    mut v_motive_3437_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3438_: *mut crate::leanh::LeanObject,
    mut v_t_3439_: *mut crate::leanh::LeanObject,
    mut v_h_3440_: *mut crate::leanh::LeanObject,
    mut v_k_3441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3442_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_3439_, v_k_3441_);
    return v___x_3442_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___boxed(
    mut v_motive_3443_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3444_: *mut crate::leanh::LeanObject,
    mut v_t_3445_: *mut crate::leanh::LeanObject,
    mut v_h_3446_: *mut crate::leanh::LeanObject,
    mut v_k_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim(
        v_motive_3443_,
        v_ctorIdx_3444_,
        v_t_3445_,
        v_h_3446_,
        v_k_3447_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3444_);
    return v_res_3448_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noEntailment_elim___redArg(
    mut v_t_3449_: *mut crate::leanh::LeanObject,
    mut v_noEntailment_3450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3451_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3449_,
        v_noEntailment_3450_,
    );
    return v___x_3451_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noEntailment_elim(
    mut v_motive_3452_: *mut crate::leanh::LeanObject,
    mut v_t_3453_: *mut crate::leanh::LeanObject,
    mut v_h_3454_: *mut crate::leanh::LeanObject,
    mut v_noEntailment_3455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3453_,
        v_noEntailment_3455_,
    );
    return v___x_3456_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noProgramFoundInTarget_elim___redArg(
    mut v_t_3457_: *mut crate::leanh::LeanObject,
    mut v_noProgramFoundInTarget_3458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3459_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3457_,
        v_noProgramFoundInTarget_3458_,
    );
    return v___x_3459_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noProgramFoundInTarget_elim(
    mut v_motive_3460_: *mut crate::leanh::LeanObject,
    mut v_t_3461_: *mut crate::leanh::LeanObject,
    mut v_h_3462_: *mut crate::leanh::LeanObject,
    mut v_noProgramFoundInTarget_3463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3464_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3461_,
        v_noProgramFoundInTarget_3463_,
    );
    return v___x_3464_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noStrategyForProgram_elim___redArg(
    mut v_t_3465_: *mut crate::leanh::LeanObject,
    mut v_noStrategyForProgram_3466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3467_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3465_,
        v_noStrategyForProgram_3466_,
    );
    return v___x_3467_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noStrategyForProgram_elim(
    mut v_motive_3468_: *mut crate::leanh::LeanObject,
    mut v_t_3469_: *mut crate::leanh::LeanObject,
    mut v_h_3470_: *mut crate::leanh::LeanObject,
    mut v_noStrategyForProgram_3471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3472_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3469_,
        v_noStrategyForProgram_3471_,
    );
    return v___x_3472_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noSpecFoundForProgram_elim___redArg(
    mut v_t_3473_: *mut crate::leanh::LeanObject,
    mut v_noSpecFoundForProgram_3474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3475_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3473_,
        v_noSpecFoundForProgram_3474_,
    );
    return v___x_3475_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noSpecFoundForProgram_elim(
    mut v_motive_3476_: *mut crate::leanh::LeanObject,
    mut v_t_3477_: *mut crate::leanh::LeanObject,
    mut v_h_3478_: *mut crate::leanh::LeanObject,
    mut v_noSpecFoundForProgram_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3480_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3477_,
        v_noSpecFoundForProgram_3479_,
    );
    return v___x_3480_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim___redArg(
    mut v_t_3481_: *mut crate::leanh::LeanObject,
    mut v_goals_3482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3483_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3481_,
        v_goals_3482_,
    );
    return v___x_3483_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim(
    mut v_motive_3484_: *mut crate::leanh::LeanObject,
    mut v_t_3485_: *mut crate::leanh::LeanObject,
    mut v_h_3486_: *mut crate::leanh::LeanObject,
    mut v_goals_3487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3488_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3485_,
        v_goals_3487_,
    );
    return v___x_3488_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(
    mut v_e_3494_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3497_: u8 = 0;
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: u8 = 0;
    let mut v_expr_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_3494_) {
                5 => {
                    v___x_3495_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2;
                    v___x_3496_ = l_Lean_Expr_isAppOf(v_e_3494_, v___x_3495_);
                    return v___x_3496_;
                }
                6 => {
                    v___x_3497_ = 0;
                    return v___x_3497_;
                }
                7 => {
                    v___x_3498_ = 0;
                    return v___x_3498_;
                }
                8 => {
                    v___x_3499_ = 0;
                    return v___x_3499_;
                }
                10 => {
                    v_expr_3500_ = crate::leanh::lean_ctor_get(v_e_3494_, 1);
                    v_e_3494_ = v_expr_3500_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_struct_3502_ = crate::leanh::lean_ctor_get(v_e_3494_, 2);
                    v_e_3494_ = v_struct_3502_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_3504_ = 1;
                    return v___x_3504_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___boxed(
    mut v_e_3505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3506_: u8 = 0;
    let mut v_r_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3506_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_e_3505_);
    crate::leanh::lean_dec_ref(v_e_3505_);
    v_r_3507_ = crate::leanh::lean_box((v_res_3506_) as usize);
    return v_r_3507_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3509_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0;
    v___x_3510_ = l_Lean_stringToMessageData(v___x_3509_);
    return v___x_3510_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(
    mut v_goal_3511_: *mut crate::leanh::LeanObject,
    mut v_target_3512_: *mut crate::leanh::LeanObject,
    mut v_a_3513_: *mut crate::leanh::LeanObject,
    mut v_a_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
    mut v_a_3517_: *mut crate::leanh::LeanObject,
    mut v_a_3518_: *mut crate::leanh::LeanObject,
    mut v_a_3519_: *mut crate::leanh::LeanObject,
    mut v_a_3520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3530_: u8 = 0;
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3535_: u8 = 0;
    let mut v_a_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3522_ = l_Lean_Expr_isForall(v_target_3512_);
                if v___x_3522_ == 0 {
                    crate::leanh::lean_dec(v_goal_3511_);
                    v___x_3523_ = crate::leanh::lean_box(0);
                    v___x_3524_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3524_, 0, v___x_3523_);
                    return v___x_3524_;
                } else {
                    v___x_3525_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1);
                    v___x_3526_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
                        v_goal_3511_,
                        v___x_3525_,
                        v_a_3513_,
                        v_a_3514_,
                        v_a_3515_,
                        v_a_3516_,
                        v_a_3517_,
                        v_a_3518_,
                        v_a_3519_,
                        v_a_3520_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3526_) == 0 {
                        v_a_3527_ = crate::leanh::lean_ctor_get(v___x_3526_, 0);
                        v_isSharedCheck_3535_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3526_)) as u8;
                        if v_isSharedCheck_3535_ == 0 {
                            v___x_3529_ = v___x_3526_;
                            v_isShared_3530_ = v_isSharedCheck_3535_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3527_);
                            crate::leanh::lean_dec(v___x_3526_);
                            v___x_3529_ = crate::leanh::lean_box(0);
                            v_isShared_3530_ = v_isSharedCheck_3535_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3536_ = crate::leanh::lean_ctor_get(v___x_3526_, 0);
                        v_isSharedCheck_3543_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3526_)) as u8;
                        if v_isSharedCheck_3543_ == 0 {
                            v___x_3538_ = v___x_3526_;
                            v_isShared_3539_ = v_isSharedCheck_3543_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3536_);
                            crate::leanh::lean_dec(v___x_3526_);
                            v___x_3538_ = crate::leanh::lean_box(0);
                            v_isShared_3539_ = v_isSharedCheck_3543_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3531_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3531_, 0, v_a_3527_);
                if v_isShared_3530_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3529_, 0, v___x_3531_);
                    v___x_3533_ = v___x_3529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
                    v___x_3533_ = v_reuseFailAlloc_3534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3533_;
            }
            3 => {
                if v_isShared_3539_ == 0 {
                    v___x_3541_ = v___x_3538_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3542_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
                    v___x_3541_ = v_reuseFailAlloc_3542_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___boxed(
    mut v_goal_3544_: *mut crate::leanh::LeanObject,
    mut v_target_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
    mut v_a_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
    mut v_a_3551_: *mut crate::leanh::LeanObject,
    mut v_a_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3555_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(v_goal_3544_, v_target_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
    crate::leanh::lean_dec(v_a_3553_);
    crate::leanh::lean_dec_ref(v_a_3552_);
    crate::leanh::lean_dec(v_a_3551_);
    crate::leanh::lean_dec_ref(v_a_3550_);
    crate::leanh::lean_dec(v_a_3549_);
    crate::leanh::lean_dec_ref(v_a_3548_);
    crate::leanh::lean_dec(v_a_3547_);
    crate::leanh::lean_dec_ref(v_a_3546_);
    crate::leanh::lean_dec_ref(v_target_3545_);
    return v_res_3555_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro(
    mut v_goal_3556_: *mut crate::leanh::LeanObject,
    mut v_target_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
    mut v_a_3560_: *mut crate::leanh::LeanObject,
    mut v_a_3561_: *mut crate::leanh::LeanObject,
    mut v_a_3562_: *mut crate::leanh::LeanObject,
    mut v_a_3563_: *mut crate::leanh::LeanObject,
    mut v_a_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
    mut v_a_3566_: *mut crate::leanh::LeanObject,
    mut v_a_3567_: *mut crate::leanh::LeanObject,
    mut v_a_3568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3570_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(v_goal_3556_, v_target_3557_, v_a_3558_, v_a_3559_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_);
    return v___x_3570_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___boxed(
    mut v_goal_3571_: *mut crate::leanh::LeanObject,
    mut v_target_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
    mut v_a_3576_: *mut crate::leanh::LeanObject,
    mut v_a_3577_: *mut crate::leanh::LeanObject,
    mut v_a_3578_: *mut crate::leanh::LeanObject,
    mut v_a_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: *mut crate::leanh::LeanObject,
    mut v_a_3581_: *mut crate::leanh::LeanObject,
    mut v_a_3582_: *mut crate::leanh::LeanObject,
    mut v_a_3583_: *mut crate::leanh::LeanObject,
    mut v_a_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3585_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro(v_goal_3571_, v_target_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
    crate::leanh::lean_dec(v_a_3583_);
    crate::leanh::lean_dec_ref(v_a_3582_);
    crate::leanh::lean_dec(v_a_3581_);
    crate::leanh::lean_dec_ref(v_a_3580_);
    crate::leanh::lean_dec(v_a_3579_);
    crate::leanh::lean_dec_ref(v_a_3578_);
    crate::leanh::lean_dec(v_a_3577_);
    crate::leanh::lean_dec_ref(v_a_3576_);
    crate::leanh::lean_dec(v_a_3575_);
    crate::leanh::lean_dec(v_a_3574_);
    crate::leanh::lean_dec_ref(v_a_3573_);
    crate::leanh::lean_dec_ref(v_target_3572_);
    return v_res_3585_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(
    mut v_msgData_3586_: *mut crate::leanh::LeanObject,
    mut v___y_3587_: *mut crate::leanh::LeanObject,
    mut v___y_3588_: *mut crate::leanh::LeanObject,
    mut v___y_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = lean_st_ref_get(v___y_3590_);
    v_env_3593_ = crate::leanh::lean_ctor_get(v___x_3592_, 0);
    crate::leanh::lean_inc_ref(v_env_3593_);
    crate::leanh::lean_dec(v___x_3592_);
    v___x_3594_ = lean_st_ref_get(v___y_3588_);
    v_mctx_3595_ = crate::leanh::lean_ctor_get(v___x_3594_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3595_);
    crate::leanh::lean_dec(v___x_3594_);
    v_lctx_3596_ = crate::leanh::lean_ctor_get(v___y_3587_, 2);
    v_options_3597_ = crate::leanh::lean_ctor_get(v___y_3589_, 2);
    crate::leanh::lean_inc_ref(v_options_3597_);
    crate::leanh::lean_inc_ref(v_lctx_3596_);
    v___x_3598_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3598_, 0, v_env_3593_);
    crate::leanh::lean_ctor_set(v___x_3598_, 1, v_mctx_3595_);
    crate::leanh::lean_ctor_set(v___x_3598_, 2, v_lctx_3596_);
    crate::leanh::lean_ctor_set(v___x_3598_, 3, v_options_3597_);
    v___x_3599_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3599_, 0, v___x_3598_);
    crate::leanh::lean_ctor_set(v___x_3599_, 1, v_msgData_3586_);
    v___x_3600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3600_, 0, v___x_3599_);
    return v___x_3600_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0___boxed(
    mut v_msgData_3601_: *mut crate::leanh::LeanObject,
    mut v___y_3602_: *mut crate::leanh::LeanObject,
    mut v___y_3603_: *mut crate::leanh::LeanObject,
    mut v___y_3604_: *mut crate::leanh::LeanObject,
    mut v___y_3605_: *mut crate::leanh::LeanObject,
    mut v___y_3606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3607_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msgData_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
    crate::leanh::lean_dec(v___y_3605_);
    crate::leanh::lean_dec_ref(v___y_3604_);
    crate::leanh::lean_dec(v___y_3603_);
    crate::leanh::lean_dec_ref(v___y_3602_);
    return v_res_3607_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: f64 = 0.0;
    v___x_3608_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3609_ = lean_float_of_nat(v___x_3608_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(
    mut v_cls_3613_: *mut crate::leanh::LeanObject,
    mut v_msg_3614_: *mut crate::leanh::LeanObject,
    mut v___y_3615_: *mut crate::leanh::LeanObject,
    mut v___y_3616_: *mut crate::leanh::LeanObject,
    mut v___y_3617_: *mut crate::leanh::LeanObject,
    mut v___y_3618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3625_: u8 = 0;
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3638_: u8 = 0;
    let mut v_tid_3639_: u64 = 0;
    let mut v_traces_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3643_: u8 = 0;
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: f64 = 0.0;
    let mut v___x_3646_: u8 = 0;
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3664_: u8 = 0;
    let mut v_isSharedCheck_3665_: u8 = 0;
    let mut v_isSharedCheck_3666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3620_ = crate::leanh::lean_ctor_get(v___y_3617_, 5);
                v___x_3621_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msg_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
                v_a_3622_ = crate::leanh::lean_ctor_get(v___x_3621_, 0);
                v_isSharedCheck_3666_ = (!crate::leanh::lean_is_exclusive(v___x_3621_)) as u8;
                if v_isSharedCheck_3666_ == 0 {
                    v___x_3624_ = v___x_3621_;
                    v_isShared_3625_ = v_isSharedCheck_3666_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3622_);
                    crate::leanh::lean_dec(v___x_3621_);
                    v___x_3624_ = crate::leanh::lean_box(0);
                    v_isShared_3625_ = v_isSharedCheck_3666_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3626_ = lean_st_ref_take(v___y_3618_);
                v_traceState_3627_ = crate::leanh::lean_ctor_get(v___x_3626_, 4);
                v_env_3628_ = crate::leanh::lean_ctor_get(v___x_3626_, 0);
                v_nextMacroScope_3629_ = crate::leanh::lean_ctor_get(v___x_3626_, 1);
                v_ngen_3630_ = crate::leanh::lean_ctor_get(v___x_3626_, 2);
                v_auxDeclNGen_3631_ = crate::leanh::lean_ctor_get(v___x_3626_, 3);
                v_cache_3632_ = crate::leanh::lean_ctor_get(v___x_3626_, 5);
                v_messages_3633_ = crate::leanh::lean_ctor_get(v___x_3626_, 6);
                v_infoState_3634_ = crate::leanh::lean_ctor_get(v___x_3626_, 7);
                v_snapshotTasks_3635_ = crate::leanh::lean_ctor_get(v___x_3626_, 8);
                v_isSharedCheck_3665_ = (!crate::leanh::lean_is_exclusive(v___x_3626_)) as u8;
                if v_isSharedCheck_3665_ == 0 {
                    v___x_3637_ = v___x_3626_;
                    v_isShared_3638_ = v_isSharedCheck_3665_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3635_);
                    crate::leanh::lean_inc(v_infoState_3634_);
                    crate::leanh::lean_inc(v_messages_3633_);
                    crate::leanh::lean_inc(v_cache_3632_);
                    crate::leanh::lean_inc(v_traceState_3627_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3631_);
                    crate::leanh::lean_inc(v_ngen_3630_);
                    crate::leanh::lean_inc(v_nextMacroScope_3629_);
                    crate::leanh::lean_inc(v_env_3628_);
                    crate::leanh::lean_dec(v___x_3626_);
                    v___x_3637_ = crate::leanh::lean_box(0);
                    v_isShared_3638_ = v_isSharedCheck_3665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3639_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3640_ = crate::leanh::lean_ctor_get(v_traceState_3627_, 0);
                v_isSharedCheck_3664_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3627_)) as u8;
                if v_isSharedCheck_3664_ == 0 {
                    v___x_3642_ = v_traceState_3627_;
                    v_isShared_3643_ = v_isSharedCheck_3664_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3640_);
                    crate::leanh::lean_dec(v_traceState_3627_);
                    v___x_3642_ = crate::leanh::lean_box(0);
                    v_isShared_3643_ = v_isSharedCheck_3664_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3644_ = crate::leanh::lean_box(0);
                v___x_3645_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0);
                v___x_3646_ = 0;
                v___x_3647_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1;
                v___x_3648_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3648_, 0, v_cls_3613_);
                crate::leanh::lean_ctor_set(v___x_3648_, 1, v___x_3644_);
                crate::leanh::lean_ctor_set(v___x_3648_, 2, v___x_3647_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3645_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3645_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3646_,
                );
                v___x_3649_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2;
                v___x_3650_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3650_, 0, v___x_3648_);
                crate::leanh::lean_ctor_set(v___x_3650_, 1, v_a_3622_);
                crate::leanh::lean_ctor_set(v___x_3650_, 2, v___x_3649_);
                crate::leanh::lean_inc(v_ref_3620_);
                v___x_3651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3651_, 0, v_ref_3620_);
                crate::leanh::lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                v___x_3652_ = l_Lean_PersistentArray_push___redArg(v_traces_3640_, v___x_3651_);
                if v_isShared_3643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3642_, 0, v___x_3652_);
                    v___x_3654_ = v___x_3642_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3652_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3663_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3639_,
                    );
                    v___x_3654_ = v_reuseFailAlloc_3663_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3637_, 4, v___x_3654_);
                    v___x_3656_ = v___x_3637_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_env_3628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_nextMacroScope_3629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 2, v_ngen_3630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 3, v_auxDeclNGen_3631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 4, v___x_3654_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 5, v_cache_3632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 6, v_messages_3633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 7, v_infoState_3634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 8, v_snapshotTasks_3635_);
                    v___x_3656_ = v_reuseFailAlloc_3662_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3657_ = lean_st_ref_set(v___y_3618_, v___x_3656_);
                v___x_3658_ = crate::leanh::lean_box(0);
                if v_isShared_3625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3624_, 0, v___x_3658_);
                    v___x_3660_ = v___x_3624_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
                    v___x_3660_ = v_reuseFailAlloc_3661_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___boxed(
    mut v_cls_3667_: *mut crate::leanh::LeanObject,
    mut v_msg_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
    mut v___y_3673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3674_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_3667_, v_msg_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
    crate::leanh::lean_dec(v___y_3672_);
    crate::leanh::lean_dec_ref(v___y_3671_);
    crate::leanh::lean_dec(v___y_3670_);
    crate::leanh::lean_dec_ref(v___y_3669_);
    return v_res_3674_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(
    mut v_msg_3675_: *mut crate::leanh::LeanObject,
    mut v___y_3676_: *mut crate::leanh::LeanObject,
    mut v___y_3677_: *mut crate::leanh::LeanObject,
    mut v___y_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3681_ = crate::leanh::lean_ctor_get(v___y_3678_, 5);
                v___x_3682_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msg_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
                v_a_3683_ = crate::leanh::lean_ctor_get(v___x_3682_, 0);
                v_isSharedCheck_3691_ = (!crate::leanh::lean_is_exclusive(v___x_3682_)) as u8;
                if v_isSharedCheck_3691_ == 0 {
                    v___x_3685_ = v___x_3682_;
                    v_isShared_3686_ = v_isSharedCheck_3691_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3683_);
                    crate::leanh::lean_dec(v___x_3682_);
                    v___x_3685_ = crate::leanh::lean_box(0);
                    v_isShared_3686_ = v_isSharedCheck_3691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3681_);
                v___x_3687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3687_, 0, v_ref_3681_);
                crate::leanh::lean_ctor_set(v___x_3687_, 1, v_a_3683_);
                if v_isShared_3686_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3685_, 1);
                    crate::leanh::lean_ctor_set(v___x_3685_, 0, v___x_3687_);
                    v___x_3689_ = v___x_3685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
                    v___x_3689_ = v_reuseFailAlloc_3690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg___boxed(
    mut v_msg_3692_: *mut crate::leanh::LeanObject,
    mut v___y_3693_: *mut crate::leanh::LeanObject,
    mut v___y_3694_: *mut crate::leanh::LeanObject,
    mut v___y_3695_: *mut crate::leanh::LeanObject,
    mut v___y_3696_: *mut crate::leanh::LeanObject,
    mut v___y_3697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3698_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v_msg_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
    crate::leanh::lean_dec(v___y_3696_);
    crate::leanh::lean_dec_ref(v___y_3695_);
    crate::leanh::lean_dec(v___y_3694_);
    crate::leanh::lean_dec_ref(v___y_3693_);
    return v_res_3698_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0;
    v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
    v___x_3715_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8;
    v___x_3716_ = l_Lean_Name_append(v___x_3715_, v___x_3714_);
    return v___x_3716_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3718_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10;
    v___x_3719_ = l_Lean_stringToMessageData(v___x_3718_);
    return v___x_3719_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12;
    v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
    return v___x_3722_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3724_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14;
    v___x_3725_ = l_Lean_stringToMessageData(v___x_3724_);
    return v___x_3725_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(
    mut v_goal_3726_: *mut crate::leanh::LeanObject,
    mut v_target_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
    mut v_a_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
    mut v_a_3732_: *mut crate::leanh::LeanObject,
    mut v_a_3733_: *mut crate::leanh::LeanObject,
    mut v_a_3734_: *mut crate::leanh::LeanObject,
    mut v_a_3735_: *mut crate::leanh::LeanObject,
    mut v_a_3736_: *mut crate::leanh::LeanObject,
    mut v_a_3737_: *mut crate::leanh::LeanObject,
    mut v_a_3738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3762_: u8 = 0;
    let mut v_a_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v___y_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3788_: u8 = 0;
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut v_a_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3801_: u8 = 0;
    let mut v_a_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3805_: u8 = 0;
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut v___y_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: u8 = 0;
    let mut v_options_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3825_: u8 = 0;
    let mut v_inheritedTraceOptions_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3838_: u8 = 0;
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v_options_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3844_: u8 = 0;
    let mut v_inheritedTraceOptions_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut v___x_3862_: u8 = 0;
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_useJP_3865_: u8 = 0;
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3862_ = l_Lean_Expr_isLet(v_target_3727_);
                if v___x_3862_ == 0 {
                    crate::leanh::lean_dec(v_goal_3726_);
                    v___x_3863_ = crate::leanh::lean_box(0);
                    v___x_3864_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3864_, 0, v___x_3863_);
                    return v___x_3864_;
                } else {
                    v_useJP_3865_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_3728_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
                    );
                    if v_useJP_3865_ == 0 {
                        v___y_3811_ = v_a_3728_;
                        v___y_3812_ = v_a_3729_;
                        v___y_3813_ = v_a_3730_;
                        v___y_3814_ = v_a_3731_;
                        v___y_3815_ = v_a_3732_;
                        v___y_3816_ = v_a_3733_;
                        v___y_3817_ = v_a_3734_;
                        v___y_3818_ = v_a_3735_;
                        v___y_3819_ = v_a_3736_;
                        v___y_3820_ = v_a_3737_;
                        v___y_3821_ = v_a_3738_;
                        state = 13;
                        continue;
                    } else {
                        v___x_3866_ = l_Lean_Expr_letName_x21(v_target_3727_);
                        crate::leanh::lean_inc(v___x_3866_);
                        v___x_3867_ = l_Lean_Elab_Tactic_Do_isJP(v___x_3866_);
                        if v___x_3867_ == 0 {
                            crate::leanh::lean_dec(v___x_3866_);
                            v___y_3811_ = v_a_3728_;
                            v___y_3812_ = v_a_3729_;
                            v___y_3813_ = v_a_3730_;
                            v___y_3814_ = v_a_3731_;
                            v___y_3815_ = v_a_3732_;
                            v___y_3816_ = v_a_3733_;
                            v___y_3817_ = v_a_3734_;
                            v___y_3818_ = v_a_3735_;
                            v___y_3819_ = v_a_3736_;
                            v___y_3820_ = v_a_3737_;
                            v___y_3821_ = v_a_3738_;
                            state = 13;
                            continue;
                        } else {
                            v___x_3868_ = l_Lean_Expr_letValue_x21(v_target_3727_);
                            v___x_3869_ = l_Lean_Expr_isLambda(v___x_3868_);
                            crate::leanh::lean_dec_ref(v___x_3868_);
                            if v___x_3869_ == 0 {
                                crate::leanh::lean_dec(v___x_3866_);
                                v___y_3811_ = v_a_3728_;
                                v___y_3812_ = v_a_3729_;
                                v___y_3813_ = v_a_3730_;
                                v___y_3814_ = v_a_3731_;
                                v___y_3815_ = v_a_3732_;
                                v___y_3816_ = v_a_3733_;
                                v___y_3817_ = v_a_3734_;
                                v___y_3818_ = v_a_3735_;
                                v___y_3819_ = v_a_3736_;
                                v___y_3820_ = v_a_3737_;
                                v___y_3821_ = v_a_3738_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_goal_3726_);
                                v___x_3870_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13);
                                v___x_3871_ = l_Lean_MessageData_ofName(v___x_3866_);
                                v___x_3872_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3872_, 0, v___x_3870_);
                                crate::leanh::lean_ctor_set(v___x_3872_, 1, v___x_3871_);
                                v___x_3873_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15);
                                v___x_3874_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3874_, 0, v___x_3872_);
                                crate::leanh::lean_ctor_set(v___x_3874_, 1, v___x_3873_);
                                v___x_3875_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_3874_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
                                v_a_3876_ = crate::leanh::lean_ctor_get(v___x_3875_, 0);
                                v_isSharedCheck_3883_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3875_)) as u8;
                                if v_isSharedCheck_3883_ == 0 {
                                    v___x_3878_ = v___x_3875_;
                                    v_isShared_3879_ = v_isSharedCheck_3883_;
                                    state = 18;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3876_);
                                    crate::leanh::lean_dec(v___x_3875_);
                                    v___x_3878_ = crate::leanh::lean_box(0);
                                    v_isShared_3879_ = v_isSharedCheck_3883_;
                                    state = 18;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3749_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1);
                v___x_3750_ = l_Lean_Expr_letName_x21(v_target_3727_);
                v___x_3751_ = l_Lean_MessageData_ofName(v___x_3750_);
                v___x_3752_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3752_, 0, v___x_3749_);
                crate::leanh::lean_ctor_set(v___x_3752_, 1, v___x_3751_);
                v___x_3753_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
                    v_goal_3726_,
                    v___x_3752_,
                    v___y_3741_,
                    v___y_3742_,
                    v___y_3743_,
                    v___y_3744_,
                    v___y_3745_,
                    v___y_3746_,
                    v___y_3747_,
                    v___y_3748_,
                );
                if crate::leanh::lean_obj_tag(v___x_3753_) == 0 {
                    v_a_3754_ = crate::leanh::lean_ctor_get(v___x_3753_, 0);
                    v_isSharedCheck_3762_ = (!crate::leanh::lean_is_exclusive(v___x_3753_)) as u8;
                    if v_isSharedCheck_3762_ == 0 {
                        v___x_3756_ = v___x_3753_;
                        v_isShared_3757_ = v_isSharedCheck_3762_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3754_);
                        crate::leanh::lean_dec(v___x_3753_);
                        v___x_3756_ = crate::leanh::lean_box(0);
                        v_isShared_3757_ = v_isSharedCheck_3762_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3763_ = crate::leanh::lean_ctor_get(v___x_3753_, 0);
                    v_isSharedCheck_3770_ = (!crate::leanh::lean_is_exclusive(v___x_3753_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3765_ = v___x_3753_;
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3763_);
                        crate::leanh::lean_dec(v___x_3753_);
                        v___x_3765_ = crate::leanh::lean_box(0);
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3758_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3758_, 0, v_a_3754_);
                if v_isShared_3757_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3756_, 0, v___x_3758_);
                    v___x_3760_ = v___x_3756_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3761_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
                    v___x_3760_ = v_reuseFailAlloc_3761_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3760_;
            }
            4 => {
                if v_isShared_3766_ == 0 {
                    v___x_3768_ = v___x_3765_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
                    v___x_3768_ = v_reuseFailAlloc_3769_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3768_;
            }
            6 => {
                v___x_3778_ = l_Lean_Expr_letBody_x21(v_target_3727_);
                v___x_3779_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3780_ = lean_mk_empty_array_with_capacity(v___x_3779_);
                v___x_3781_ = lean_array_push(v___x_3780_, v___y_3772_);
                v___x_3782_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                    v___x_3778_,
                    v___x_3781_,
                    v___y_3773_,
                );
                crate::leanh::lean_dec_ref(v___x_3781_);
                if crate::leanh::lean_obj_tag(v___x_3782_) == 0 {
                    v_a_3783_ = crate::leanh::lean_ctor_get(v___x_3782_, 0);
                    crate::leanh::lean_inc(v_a_3783_);
                    crate::leanh::lean_dec_ref_known(v___x_3782_, 1);
                    v___x_3784_ = l_Lean_MVarId_replaceTargetDefEq(
                        v_goal_3726_,
                        v_a_3783_,
                        v___y_3774_,
                        v___y_3775_,
                        v___y_3776_,
                        v___y_3777_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3784_) == 0 {
                        v_a_3785_ = crate::leanh::lean_ctor_get(v___x_3784_, 0);
                        v_isSharedCheck_3793_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3784_)) as u8;
                        if v_isSharedCheck_3793_ == 0 {
                            v___x_3787_ = v___x_3784_;
                            v_isShared_3788_ = v_isSharedCheck_3793_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3785_);
                            crate::leanh::lean_dec(v___x_3784_);
                            v___x_3787_ = crate::leanh::lean_box(0);
                            v_isShared_3788_ = v_isSharedCheck_3793_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_a_3794_ = crate::leanh::lean_ctor_get(v___x_3784_, 0);
                        v_isSharedCheck_3801_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3784_)) as u8;
                        if v_isSharedCheck_3801_ == 0 {
                            v___x_3796_ = v___x_3784_;
                            v_isShared_3797_ = v_isSharedCheck_3801_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3794_);
                            crate::leanh::lean_dec(v___x_3784_);
                            v___x_3796_ = crate::leanh::lean_box(0);
                            v_isShared_3797_ = v_isSharedCheck_3801_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_3726_);
                    v_a_3802_ = crate::leanh::lean_ctor_get(v___x_3782_, 0);
                    v_isSharedCheck_3809_ = (!crate::leanh::lean_is_exclusive(v___x_3782_)) as u8;
                    if v_isSharedCheck_3809_ == 0 {
                        v___x_3804_ = v___x_3782_;
                        v_isShared_3805_ = v_isSharedCheck_3809_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3802_);
                        crate::leanh::lean_dec(v___x_3782_);
                        v___x_3804_ = crate::leanh::lean_box(0);
                        v_isShared_3805_ = v_isSharedCheck_3809_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3789_, 0, v_a_3785_);
                if v_isShared_3788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3787_, 0, v___x_3789_);
                    v___x_3791_ = v___x_3787_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3792_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
                    v___x_3791_ = v_reuseFailAlloc_3792_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3791_;
            }
            9 => {
                if v_isShared_3797_ == 0 {
                    v___x_3799_ = v___x_3796_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
                    v___x_3799_ = v_reuseFailAlloc_3800_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3799_;
            }
            11 => {
                if v_isShared_3805_ == 0 {
                    v___x_3807_ = v___x_3804_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
                    v___x_3807_ = v_reuseFailAlloc_3808_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3807_;
            }
            13 => {
                v___x_3822_ = l_Lean_Expr_letValue_x21(v_target_3727_);
                v___x_3823_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v___x_3822_);
                if v___x_3823_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3822_);
                    v_options_3824_ = crate::leanh::lean_ctor_get(v___y_3820_, 2);
                    v_hasTrace_3825_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_3824_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3825_ == 0 {
                        v___y_3741_ = v___y_3811_;
                        v___y_3742_ = v___y_3812_;
                        v___y_3743_ = v___y_3816_;
                        v___y_3744_ = v___y_3817_;
                        v___y_3745_ = v___y_3818_;
                        v___y_3746_ = v___y_3819_;
                        v___y_3747_ = v___y_3820_;
                        v___y_3748_ = v___y_3821_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_3826_ =
                            crate::leanh::lean_ctor_get(v___y_3820_, 13);
                        v___x_3827_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                        v___x_3828_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
                        v___x_3829_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3826_,
                            v_options_3824_,
                            v___x_3828_,
                        );
                        if v___x_3829_ == 0 {
                            v___y_3741_ = v___y_3811_;
                            v___y_3742_ = v___y_3812_;
                            v___y_3743_ = v___y_3816_;
                            v___y_3744_ = v___y_3817_;
                            v___y_3745_ = v___y_3818_;
                            v___y_3746_ = v___y_3819_;
                            v___y_3747_ = v___y_3820_;
                            v___y_3748_ = v___y_3821_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3830_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1);
                            v___x_3831_ = l_Lean_Expr_letName_x21(v_target_3727_);
                            v___x_3832_ = l_Lean_MessageData_ofName(v___x_3831_);
                            v___x_3833_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3833_, 0, v___x_3830_);
                            crate::leanh::lean_ctor_set(v___x_3833_, 1, v___x_3832_);
                            v___x_3834_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_3827_, v___x_3833_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
                            if crate::leanh::lean_obj_tag(v___x_3834_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3834_, 1);
                                v___y_3741_ = v___y_3811_;
                                v___y_3742_ = v___y_3812_;
                                v___y_3743_ = v___y_3816_;
                                v___y_3744_ = v___y_3817_;
                                v___y_3745_ = v___y_3818_;
                                v___y_3746_ = v___y_3819_;
                                v___y_3747_ = v___y_3820_;
                                v___y_3748_ = v___y_3821_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_goal_3726_);
                                v_a_3835_ = crate::leanh::lean_ctor_get(v___x_3834_, 0);
                                v_isSharedCheck_3842_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3834_)) as u8;
                                if v_isSharedCheck_3842_ == 0 {
                                    v___x_3837_ = v___x_3834_;
                                    v_isShared_3838_ = v_isSharedCheck_3842_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3835_);
                                    crate::leanh::lean_dec(v___x_3834_);
                                    v___x_3837_ = crate::leanh::lean_box(0);
                                    v_isShared_3838_ = v_isSharedCheck_3842_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v_options_3843_ = crate::leanh::lean_ctor_get(v___y_3820_, 2);
                    v_hasTrace_3844_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_3843_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3844_ == 0 {
                        v___y_3772_ = v___x_3822_;
                        v___y_3773_ = v___y_3817_;
                        v___y_3774_ = v___y_3818_;
                        v___y_3775_ = v___y_3819_;
                        v___y_3776_ = v___y_3820_;
                        v___y_3777_ = v___y_3821_;
                        state = 6;
                        continue;
                    } else {
                        v_inheritedTraceOptions_3845_ =
                            crate::leanh::lean_ctor_get(v___y_3820_, 13);
                        v___x_3846_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                        v___x_3847_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
                        v___x_3848_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3845_,
                            v_options_3843_,
                            v___x_3847_,
                        );
                        if v___x_3848_ == 0 {
                            v___y_3772_ = v___x_3822_;
                            v___y_3773_ = v___y_3817_;
                            v___y_3774_ = v___y_3818_;
                            v___y_3775_ = v___y_3819_;
                            v___y_3776_ = v___y_3820_;
                            v___y_3777_ = v___y_3821_;
                            state = 6;
                            continue;
                        } else {
                            v___x_3849_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11);
                            v___x_3850_ = l_Lean_Expr_letName_x21(v_target_3727_);
                            v___x_3851_ = l_Lean_MessageData_ofName(v___x_3850_);
                            v___x_3852_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3852_, 0, v___x_3849_);
                            crate::leanh::lean_ctor_set(v___x_3852_, 1, v___x_3851_);
                            v___x_3853_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_3846_, v___x_3852_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
                            if crate::leanh::lean_obj_tag(v___x_3853_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3853_, 1);
                                v___y_3772_ = v___x_3822_;
                                v___y_3773_ = v___y_3817_;
                                v___y_3774_ = v___y_3818_;
                                v___y_3775_ = v___y_3819_;
                                v___y_3776_ = v___y_3820_;
                                v___y_3777_ = v___y_3821_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3822_);
                                crate::leanh::lean_dec(v_goal_3726_);
                                v_a_3854_ = crate::leanh::lean_ctor_get(v___x_3853_, 0);
                                v_isSharedCheck_3861_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3853_)) as u8;
                                if v_isSharedCheck_3861_ == 0 {
                                    v___x_3856_ = v___x_3853_;
                                    v_isShared_3857_ = v_isSharedCheck_3861_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3854_);
                                    crate::leanh::lean_dec(v___x_3853_);
                                    v___x_3856_ = crate::leanh::lean_box(0);
                                    v_isShared_3857_ = v_isSharedCheck_3861_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            14 => {
                if v_isShared_3838_ == 0 {
                    v___x_3840_ = v___x_3837_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
                    v___x_3840_ = v_reuseFailAlloc_3841_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3840_;
            }
            16 => {
                if v_isShared_3857_ == 0 {
                    v___x_3859_ = v___x_3856_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
                    v___x_3859_ = v_reuseFailAlloc_3860_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3859_;
            }
            18 => {
                if v_isShared_3879_ == 0 {
                    v___x_3881_ = v___x_3878_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3882_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
                    v___x_3881_ = v_reuseFailAlloc_3882_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3881_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___boxed(
    mut v_goal_3884_: *mut crate::leanh::LeanObject,
    mut v_target_3885_: *mut crate::leanh::LeanObject,
    mut v_a_3886_: *mut crate::leanh::LeanObject,
    mut v_a_3887_: *mut crate::leanh::LeanObject,
    mut v_a_3888_: *mut crate::leanh::LeanObject,
    mut v_a_3889_: *mut crate::leanh::LeanObject,
    mut v_a_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
    mut v_a_3894_: *mut crate::leanh::LeanObject,
    mut v_a_3895_: *mut crate::leanh::LeanObject,
    mut v_a_3896_: *mut crate::leanh::LeanObject,
    mut v_a_3897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3898_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(v_goal_3884_, v_target_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
    crate::leanh::lean_dec(v_a_3896_);
    crate::leanh::lean_dec_ref(v_a_3895_);
    crate::leanh::lean_dec(v_a_3894_);
    crate::leanh::lean_dec_ref(v_a_3893_);
    crate::leanh::lean_dec(v_a_3892_);
    crate::leanh::lean_dec_ref(v_a_3891_);
    crate::leanh::lean_dec(v_a_3890_);
    crate::leanh::lean_dec_ref(v_a_3889_);
    crate::leanh::lean_dec(v_a_3888_);
    crate::leanh::lean_dec(v_a_3887_);
    crate::leanh::lean_dec_ref(v_a_3886_);
    crate::leanh::lean_dec_ref(v_target_3885_);
    return v_res_3898_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0(
    mut v_cls_3899_: *mut crate::leanh::LeanObject,
    mut v_msg_3900_: *mut crate::leanh::LeanObject,
    mut v___y_3901_: *mut crate::leanh::LeanObject,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
    mut v___y_3903_: *mut crate::leanh::LeanObject,
    mut v___y_3904_: *mut crate::leanh::LeanObject,
    mut v___y_3905_: *mut crate::leanh::LeanObject,
    mut v___y_3906_: *mut crate::leanh::LeanObject,
    mut v___y_3907_: *mut crate::leanh::LeanObject,
    mut v___y_3908_: *mut crate::leanh::LeanObject,
    mut v___y_3909_: *mut crate::leanh::LeanObject,
    mut v___y_3910_: *mut crate::leanh::LeanObject,
    mut v___y_3911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3913_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_3899_, v_msg_3900_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
    return v___x_3913_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___boxed(
    mut v_cls_3914_: *mut crate::leanh::LeanObject,
    mut v_msg_3915_: *mut crate::leanh::LeanObject,
    mut v___y_3916_: *mut crate::leanh::LeanObject,
    mut v___y_3917_: *mut crate::leanh::LeanObject,
    mut v___y_3918_: *mut crate::leanh::LeanObject,
    mut v___y_3919_: *mut crate::leanh::LeanObject,
    mut v___y_3920_: *mut crate::leanh::LeanObject,
    mut v___y_3921_: *mut crate::leanh::LeanObject,
    mut v___y_3922_: *mut crate::leanh::LeanObject,
    mut v___y_3923_: *mut crate::leanh::LeanObject,
    mut v___y_3924_: *mut crate::leanh::LeanObject,
    mut v___y_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3928_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0(v_cls_3914_, v_msg_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
    crate::leanh::lean_dec(v___y_3926_);
    crate::leanh::lean_dec_ref(v___y_3925_);
    crate::leanh::lean_dec(v___y_3924_);
    crate::leanh::lean_dec_ref(v___y_3923_);
    crate::leanh::lean_dec(v___y_3922_);
    crate::leanh::lean_dec_ref(v___y_3921_);
    crate::leanh::lean_dec(v___y_3920_);
    crate::leanh::lean_dec_ref(v___y_3919_);
    crate::leanh::lean_dec(v___y_3918_);
    crate::leanh::lean_dec(v___y_3917_);
    crate::leanh::lean_dec_ref(v___y_3916_);
    return v_res_3928_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1(
    mut v_00_u03b1_3929_: *mut crate::leanh::LeanObject,
    mut v_msg_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
    mut v___y_3932_: *mut crate::leanh::LeanObject,
    mut v___y_3933_: *mut crate::leanh::LeanObject,
    mut v___y_3934_: *mut crate::leanh::LeanObject,
    mut v___y_3935_: *mut crate::leanh::LeanObject,
    mut v___y_3936_: *mut crate::leanh::LeanObject,
    mut v___y_3937_: *mut crate::leanh::LeanObject,
    mut v___y_3938_: *mut crate::leanh::LeanObject,
    mut v___y_3939_: *mut crate::leanh::LeanObject,
    mut v___y_3940_: *mut crate::leanh::LeanObject,
    mut v___y_3941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v_msg_3930_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
    return v___x_3943_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___boxed(
    mut v_00_u03b1_3944_: *mut crate::leanh::LeanObject,
    mut v_msg_3945_: *mut crate::leanh::LeanObject,
    mut v___y_3946_: *mut crate::leanh::LeanObject,
    mut v___y_3947_: *mut crate::leanh::LeanObject,
    mut v___y_3948_: *mut crate::leanh::LeanObject,
    mut v___y_3949_: *mut crate::leanh::LeanObject,
    mut v___y_3950_: *mut crate::leanh::LeanObject,
    mut v___y_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
    mut v___y_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3958_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1(v_00_u03b1_3944_, v_msg_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
    crate::leanh::lean_dec(v___y_3956_);
    crate::leanh::lean_dec_ref(v___y_3955_);
    crate::leanh::lean_dec(v___y_3954_);
    crate::leanh::lean_dec_ref(v___y_3953_);
    crate::leanh::lean_dec(v___y_3952_);
    crate::leanh::lean_dec_ref(v___y_3951_);
    crate::leanh::lean_dec(v___y_3950_);
    crate::leanh::lean_dec_ref(v___y_3949_);
    crate::leanh::lean_dec(v___y_3948_);
    crate::leanh::lean_dec(v___y_3947_);
    crate::leanh::lean_dec_ref(v___y_3946_);
    return v_res_3958_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(
    mut v_goal_3965_: *mut crate::leanh::LeanObject,
    mut v_target_3966_: *mut crate::leanh::LeanObject,
    mut v_a_3967_: *mut crate::leanh::LeanObject,
    mut v_a_3968_: *mut crate::leanh::LeanObject,
    mut v_a_3969_: *mut crate::leanh::LeanObject,
    mut v_a_3970_: *mut crate::leanh::LeanObject,
    mut v_a_3971_: *mut crate::leanh::LeanObject,
    mut v_a_3972_: *mut crate::leanh::LeanObject,
    mut v_a_3973_: *mut crate::leanh::LeanObject,
    mut v_a_3974_: *mut crate::leanh::LeanObject,
    mut v_a_3975_: *mut crate::leanh::LeanObject,
    mut v_a_3976_: *mut crate::leanh::LeanObject,
    mut v_a_3977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: u8 = 0;
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3988_: u8 = 0;
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3993_: u8 = 0;
    let mut v_a_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3997_: u8 = 0;
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3979_ = l_Lean_Expr_getAppFn(v_target_3966_);
                v___x_3980_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2;
                v___x_3981_ = l_Lean_Expr_isConstOf(v___x_3979_, v___x_3980_);
                crate::leanh::lean_dec_ref(v___x_3979_);
                if v___x_3981_ == 0 {
                    crate::leanh::lean_dec(v_goal_3965_);
                    v___x_3982_ = crate::leanh::lean_box(0);
                    v___x_3983_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3983_, 0, v___x_3982_);
                    return v___x_3983_;
                } else {
                    v___x_3984_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP(
                        v_goal_3965_,
                        v_a_3967_,
                        v_a_3968_,
                        v_a_3969_,
                        v_a_3970_,
                        v_a_3971_,
                        v_a_3972_,
                        v_a_3973_,
                        v_a_3974_,
                        v_a_3975_,
                        v_a_3976_,
                        v_a_3977_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3984_) == 0 {
                        v_a_3985_ = crate::leanh::lean_ctor_get(v___x_3984_, 0);
                        v_isSharedCheck_3993_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3984_)) as u8;
                        if v_isSharedCheck_3993_ == 0 {
                            v___x_3987_ = v___x_3984_;
                            v_isShared_3988_ = v_isSharedCheck_3993_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3985_);
                            crate::leanh::lean_dec(v___x_3984_);
                            v___x_3987_ = crate::leanh::lean_box(0);
                            v_isShared_3988_ = v_isSharedCheck_3993_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3994_ = crate::leanh::lean_ctor_get(v___x_3984_, 0);
                        v_isSharedCheck_4001_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3984_)) as u8;
                        if v_isSharedCheck_4001_ == 0 {
                            v___x_3996_ = v___x_3984_;
                            v_isShared_3997_ = v_isSharedCheck_4001_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3994_);
                            crate::leanh::lean_dec(v___x_3984_);
                            v___x_3996_ = crate::leanh::lean_box(0);
                            v_isShared_3997_ = v_isSharedCheck_4001_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3989_, 0, v_a_3985_);
                if v_isShared_3988_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3987_, 0, v___x_3989_);
                    v___x_3991_ = v___x_3987_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3989_);
                    v___x_3991_ = v_reuseFailAlloc_3992_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3991_;
            }
            3 => {
                if v_isShared_3997_ == 0 {
                    v___x_3999_ = v___x_3996_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4000_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
                    v___x_3999_ = v_reuseFailAlloc_4000_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___boxed(
    mut v_goal_4002_: *mut crate::leanh::LeanObject,
    mut v_target_4003_: *mut crate::leanh::LeanObject,
    mut v_a_4004_: *mut crate::leanh::LeanObject,
    mut v_a_4005_: *mut crate::leanh::LeanObject,
    mut v_a_4006_: *mut crate::leanh::LeanObject,
    mut v_a_4007_: *mut crate::leanh::LeanObject,
    mut v_a_4008_: *mut crate::leanh::LeanObject,
    mut v_a_4009_: *mut crate::leanh::LeanObject,
    mut v_a_4010_: *mut crate::leanh::LeanObject,
    mut v_a_4011_: *mut crate::leanh::LeanObject,
    mut v_a_4012_: *mut crate::leanh::LeanObject,
    mut v_a_4013_: *mut crate::leanh::LeanObject,
    mut v_a_4014_: *mut crate::leanh::LeanObject,
    mut v_a_4015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4016_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(v_goal_4002_, v_target_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
    crate::leanh::lean_dec(v_a_4014_);
    crate::leanh::lean_dec_ref(v_a_4013_);
    crate::leanh::lean_dec(v_a_4012_);
    crate::leanh::lean_dec_ref(v_a_4011_);
    crate::leanh::lean_dec(v_a_4010_);
    crate::leanh::lean_dec_ref(v_a_4009_);
    crate::leanh::lean_dec(v_a_4008_);
    crate::leanh::lean_dec_ref(v_a_4007_);
    crate::leanh::lean_dec(v_a_4006_);
    crate::leanh::lean_dec(v_a_4005_);
    crate::leanh::lean_dec_ref(v_a_4004_);
    crate::leanh::lean_dec_ref(v_target_4003_);
    return v_res_4016_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4018_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0;
    v___x_4019_ = l_Lean_stringToMessageData(v___x_4018_);
    return v___x_4019_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4027_: u8 = 0;
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4027_ = 0;
    v___x_4028_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4;
    v___x_4029_ = l_Lean_MessageData_ofConstName(v___x_4028_, v___x_4027_);
    return v___x_4029_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4030_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5);
    v___x_4031_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1);
    v___x_4032_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4032_, 0, v___x_4031_);
    crate::leanh::lean_ctor_set(v___x_4032_, 1, v___x_4030_);
    return v___x_4032_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4034_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7;
    v___x_4035_ = l_Lean_stringToMessageData(v___x_4034_);
    return v___x_4035_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4036_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8);
    v___x_4037_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6);
    v___x_4038_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4038_, 0, v___x_4037_);
    crate::leanh::lean_ctor_set(v___x_4038_, 1, v___x_4036_);
    return v___x_4038_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4040_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10;
    v___x_4041_ = l_Lean_stringToMessageData(v___x_4040_);
    return v___x_4041_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(
    mut v_goal_4042_: *mut crate::leanh::LeanObject,
    mut v_T_4043_: *mut crate::leanh::LeanObject,
    mut v_a_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v_a_4046_: *mut crate::leanh::LeanObject,
    mut v_a_4047_: *mut crate::leanh::LeanObject,
    mut v_a_4048_: *mut crate::leanh::LeanObject,
    mut v_a_4049_: *mut crate::leanh::LeanObject,
    mut v_a_4050_: *mut crate::leanh::LeanObject,
    mut v_a_4051_: *mut crate::leanh::LeanObject,
    mut v_a_4052_: *mut crate::leanh::LeanObject,
    mut v_a_4053_: *mut crate::leanh::LeanObject,
    mut v_a_4054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4056_: u8 = 0;
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entailsConsIntroRule_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4065_: u8 = 0;
    let mut v___y_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4082_: u8 = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v_mvarIds_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4090_: u8 = 0;
    let mut v_tail_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut v_isSharedCheck_4100_: u8 = 0;
    let mut v_a_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4056_ = l_Lean_Expr_isLambda(v_T_4043_);
                if v___x_4056_ == 0 {
                    crate::leanh::lean_dec(v_goal_4042_);
                    v___x_4057_ = crate::leanh::lean_box(0);
                    v___x_4058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4058_, 0, v___x_4057_);
                    return v___x_4058_;
                } else {
                    v_entailsConsIntroRule_4059_ = crate::leanh::lean_ctor_get(v_a_4044_, 0);
                    v___x_4060_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_goal_4042_);
                    crate::leanh::lean_inc_ref(v_entailsConsIntroRule_4059_);
                    v___x_4061_ =
                        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                            v_entailsConsIntroRule_4059_,
                            v_goal_4042_,
                            v___x_4060_,
                            v_a_4044_,
                            v_a_4045_,
                            v_a_4046_,
                            v_a_4047_,
                            v_a_4048_,
                            v_a_4049_,
                            v_a_4050_,
                            v_a_4051_,
                            v_a_4052_,
                            v_a_4053_,
                            v_a_4054_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4061_) == 0 {
                        v_a_4062_ = crate::leanh::lean_ctor_get(v___x_4061_, 0);
                        v_isSharedCheck_4100_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4061_)) as u8;
                        if v_isSharedCheck_4100_ == 0 {
                            v___x_4064_ = v___x_4061_;
                            v_isShared_4065_ = v_isSharedCheck_4100_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4062_);
                            crate::leanh::lean_dec(v___x_4061_);
                            v___x_4064_ = crate::leanh::lean_box(0);
                            v_isShared_4065_ = v_isSharedCheck_4100_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_goal_4042_);
                        v_a_4101_ = crate::leanh::lean_ctor_get(v___x_4061_, 0);
                        v_isSharedCheck_4108_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4061_)) as u8;
                        if v_isSharedCheck_4108_ == 0 {
                            v___x_4103_ = v___x_4061_;
                            v_isShared_4104_ = v_isSharedCheck_4108_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4101_);
                            crate::leanh::lean_dec(v___x_4061_);
                            v___x_4103_ = crate::leanh::lean_box(0);
                            v_isShared_4104_ = v_isSharedCheck_4108_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4062_) == 1 {
                    v_mvarIds_4087_ = crate::leanh::lean_ctor_get(v_a_4062_, 0);
                    v_isSharedCheck_4099_ = (!crate::leanh::lean_is_exclusive(v_a_4062_)) as u8;
                    if v_isSharedCheck_4099_ == 0 {
                        v___x_4089_ = v_a_4062_;
                        v_isShared_4090_ = v_isSharedCheck_4099_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarIds_4087_);
                        crate::leanh::lean_dec(v_a_4062_);
                        v___x_4089_ = crate::leanh::lean_box(0);
                        v_isShared_4090_ = v_isSharedCheck_4099_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4064_);
                    crate::leanh::lean_dec(v_a_4062_);
                    v___y_4067_ = v_a_4051_;
                    v___y_4068_ = v_a_4052_;
                    v___y_4069_ = v_a_4053_;
                    v___y_4070_ = v_a_4054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4071_ = l_Lean_MVarId_getType(
                    v_goal_4042_,
                    v___y_4067_,
                    v___y_4068_,
                    v___y_4069_,
                    v___y_4070_,
                );
                if crate::leanh::lean_obj_tag(v___x_4071_) == 0 {
                    v_a_4072_ = crate::leanh::lean_ctor_get(v___x_4071_, 0);
                    crate::leanh::lean_inc(v_a_4072_);
                    crate::leanh::lean_dec_ref_known(v___x_4071_, 1);
                    v___x_4073_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9);
                    v___x_4074_ = l_Lean_MessageData_ofExpr(v_a_4072_);
                    v___x_4075_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4075_, 0, v___x_4073_);
                    crate::leanh::lean_ctor_set(v___x_4075_, 1, v___x_4074_);
                    v___x_4076_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11);
                    v___x_4077_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4077_, 0, v___x_4075_);
                    crate::leanh::lean_ctor_set(v___x_4077_, 1, v___x_4076_);
                    v___x_4078_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_4077_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
                    return v___x_4078_;
                } else {
                    v_a_4079_ = crate::leanh::lean_ctor_get(v___x_4071_, 0);
                    v_isSharedCheck_4086_ = (!crate::leanh::lean_is_exclusive(v___x_4071_)) as u8;
                    if v_isSharedCheck_4086_ == 0 {
                        v___x_4081_ = v___x_4071_;
                        v_isShared_4082_ = v_isSharedCheck_4086_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4079_);
                        crate::leanh::lean_dec(v___x_4071_);
                        v___x_4081_ = crate::leanh::lean_box(0);
                        v_isShared_4082_ = v_isSharedCheck_4086_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4082_ == 0 {
                    v___x_4084_ = v___x_4081_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
                    v___x_4084_ = v_reuseFailAlloc_4085_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4084_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_mvarIds_4087_) == 1 {
                    v_tail_4091_ = crate::leanh::lean_ctor_get(v_mvarIds_4087_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_4091_) == 0 {
                        crate::leanh::lean_dec(v_goal_4042_);
                        v_head_4092_ = crate::leanh::lean_ctor_get(v_mvarIds_4087_, 0);
                        crate::leanh::lean_inc(v_head_4092_);
                        crate::leanh::lean_dec_ref_known(v_mvarIds_4087_, 2);
                        if v_isShared_4090_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4089_, 0, v_head_4092_);
                            v___x_4094_ = v___x_4089_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4098_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_head_4092_);
                            v___x_4094_ = v_reuseFailAlloc_4098_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_mvarIds_4087_, 2);
                        crate::leanh::lean_del_object(v___x_4089_);
                        crate::leanh::lean_del_object(v___x_4064_);
                        v___y_4067_ = v_a_4051_;
                        v___y_4068_ = v_a_4052_;
                        v___y_4069_ = v_a_4053_;
                        v___y_4070_ = v_a_4054_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4089_);
                    crate::leanh::lean_dec(v_mvarIds_4087_);
                    crate::leanh::lean_del_object(v___x_4064_);
                    v___y_4067_ = v_a_4051_;
                    v___y_4068_ = v_a_4052_;
                    v___y_4069_ = v_a_4053_;
                    v___y_4070_ = v_a_4054_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_4065_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4064_, 0, v___x_4094_);
                    v___x_4096_ = v___x_4064_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4097_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4094_);
                    v___x_4096_ = v_reuseFailAlloc_4097_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4096_;
            }
            8 => {
                if v_isShared_4104_ == 0 {
                    v___x_4106_ = v___x_4103_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4107_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
                    v___x_4106_ = v_reuseFailAlloc_4107_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4106_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___boxed(
    mut v_goal_4109_: *mut crate::leanh::LeanObject,
    mut v_T_4110_: *mut crate::leanh::LeanObject,
    mut v_a_4111_: *mut crate::leanh::LeanObject,
    mut v_a_4112_: *mut crate::leanh::LeanObject,
    mut v_a_4113_: *mut crate::leanh::LeanObject,
    mut v_a_4114_: *mut crate::leanh::LeanObject,
    mut v_a_4115_: *mut crate::leanh::LeanObject,
    mut v_a_4116_: *mut crate::leanh::LeanObject,
    mut v_a_4117_: *mut crate::leanh::LeanObject,
    mut v_a_4118_: *mut crate::leanh::LeanObject,
    mut v_a_4119_: *mut crate::leanh::LeanObject,
    mut v_a_4120_: *mut crate::leanh::LeanObject,
    mut v_a_4121_: *mut crate::leanh::LeanObject,
    mut v_a_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4123_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(v_goal_4109_, v_T_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
    crate::leanh::lean_dec(v_a_4121_);
    crate::leanh::lean_dec_ref(v_a_4120_);
    crate::leanh::lean_dec(v_a_4119_);
    crate::leanh::lean_dec_ref(v_a_4118_);
    crate::leanh::lean_dec(v_a_4117_);
    crate::leanh::lean_dec_ref(v_a_4116_);
    crate::leanh::lean_dec(v_a_4115_);
    crate::leanh::lean_dec_ref(v_a_4114_);
    crate::leanh::lean_dec(v_a_4113_);
    crate::leanh::lean_dec(v_a_4112_);
    crate::leanh::lean_dec_ref(v_a_4111_);
    crate::leanh::lean_dec_ref(v_T_4110_);
    return v_res_4123_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(
    mut v_f_4124_: *mut crate::leanh::LeanObject,
    mut v_a_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4138_: u8 = 0;
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4137_ = lean_st_ref_get(v___y_4127_);
                v_debug_4138_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4137_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_4137_);
                if v_debug_4138_ == 0 {
                    v___y_4134_ = v___y_4127_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_4124_);
                    v___x_4139_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_4124_,
                        v___y_4126_,
                        v___y_4127_,
                        v___y_4128_,
                        v___y_4129_,
                        v___y_4130_,
                        v___y_4131_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4139_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4139_, 1);
                        crate::leanh::lean_inc_ref(v_a_4125_);
                        v___x_4140_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_4125_,
                            v___y_4126_,
                            v___y_4127_,
                            v___y_4128_,
                            v___y_4129_,
                            v___y_4130_,
                            v___y_4131_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4140_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4140_, 1);
                            v___y_4134_ = v___y_4127_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_4125_);
                            crate::leanh::lean_dec_ref(v_f_4124_);
                            v_a_4141_ = crate::leanh::lean_ctor_get(v___x_4140_, 0);
                            v_isSharedCheck_4148_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4140_)) as u8;
                            if v_isSharedCheck_4148_ == 0 {
                                v___x_4143_ = v___x_4140_;
                                v_isShared_4144_ = v_isSharedCheck_4148_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4141_);
                                crate::leanh::lean_dec(v___x_4140_);
                                v___x_4143_ = crate::leanh::lean_box(0);
                                v_isShared_4144_ = v_isSharedCheck_4148_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_4125_);
                        crate::leanh::lean_dec_ref(v_f_4124_);
                        v_a_4149_ = crate::leanh::lean_ctor_get(v___x_4139_, 0);
                        v_isSharedCheck_4156_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4139_)) as u8;
                        if v_isSharedCheck_4156_ == 0 {
                            v___x_4151_ = v___x_4139_;
                            v_isShared_4152_ = v_isSharedCheck_4156_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4149_);
                            crate::leanh::lean_dec(v___x_4139_);
                            v___x_4151_ = crate::leanh::lean_box(0);
                            v_isShared_4152_ = v_isSharedCheck_4156_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4135_ = l_Lean_Expr_app___override(v_f_4124_, v_a_4125_);
                v___x_4136_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_4135_, v___y_4134_);
                return v___x_4136_;
            }
            2 => {
                if v_isShared_4144_ == 0 {
                    v___x_4146_ = v___x_4143_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
                    v___x_4146_ = v_reuseFailAlloc_4147_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4146_;
            }
            4 => {
                if v_isShared_4152_ == 0 {
                    v___x_4154_ = v___x_4151_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
                    v___x_4154_ = v_reuseFailAlloc_4155_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg___boxed(
    mut v_f_4157_: *mut crate::leanh::LeanObject,
    mut v_a_4158_: *mut crate::leanh::LeanObject,
    mut v___y_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
    mut v___y_4165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4166_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_4157_, v_a_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
    crate::leanh::lean_dec(v___y_4164_);
    crate::leanh::lean_dec_ref(v___y_4163_);
    crate::leanh::lean_dec(v___y_4162_);
    crate::leanh::lean_dec_ref(v___y_4161_);
    crate::leanh::lean_dec(v___y_4160_);
    crate::leanh::lean_dec_ref(v___y_4159_);
    return v_res_4166_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(
    mut v_f_4167_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_4168_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
    mut v___y_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4182_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_4167_, v_a_u2081_4168_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
    if crate::leanh::lean_obj_tag(v___x_4182_) == 0 {
        let mut v_a_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4183_ = crate::leanh::lean_ctor_get(v___x_4182_, 0);
        crate::leanh::lean_inc(v_a_4183_);
        crate::leanh::lean_dec_ref_known(v___x_4182_, 1);
        v___x_4184_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_4183_, v_a_u2082_4169_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
        return v___x_4184_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2082_4169_);
        return v___x_4182_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0___boxed(
    mut v_f_4185_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_4186_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
    mut v___y_4194_: *mut crate::leanh::LeanObject,
    mut v___y_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4200_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(v_f_4185_, v_a_u2081_4186_, v_a_u2082_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
    crate::leanh::lean_dec(v___y_4198_);
    crate::leanh::lean_dec_ref(v___y_4197_);
    crate::leanh::lean_dec(v___y_4196_);
    crate::leanh::lean_dec_ref(v___y_4195_);
    crate::leanh::lean_dec(v___y_4194_);
    crate::leanh::lean_dec_ref(v___y_4193_);
    crate::leanh::lean_dec(v___y_4192_);
    crate::leanh::lean_dec_ref(v___y_4191_);
    crate::leanh::lean_dec(v___y_4190_);
    crate::leanh::lean_dec(v___y_4189_);
    crate::leanh::lean_dec_ref(v___y_4188_);
    return v_res_4200_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(
    mut v_f_4201_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_4202_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_4203_: *mut crate::leanh::LeanObject,
    mut v_a_u2083_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
    mut v___y_4209_: *mut crate::leanh::LeanObject,
    mut v___y_4210_: *mut crate::leanh::LeanObject,
    mut v___y_4211_: *mut crate::leanh::LeanObject,
    mut v___y_4212_: *mut crate::leanh::LeanObject,
    mut v___y_4213_: *mut crate::leanh::LeanObject,
    mut v___y_4214_: *mut crate::leanh::LeanObject,
    mut v___y_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4217_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(v_f_4201_, v_a_u2081_4202_, v_a_u2082_4203_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
    if crate::leanh::lean_obj_tag(v___x_4217_) == 0 {
        let mut v_a_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4218_ = crate::leanh::lean_ctor_get(v___x_4217_, 0);
        crate::leanh::lean_inc(v_a_4218_);
        crate::leanh::lean_dec_ref_known(v___x_4217_, 1);
        v___x_4219_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_4218_, v_a_u2083_4204_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
        return v___x_4219_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2083_4204_);
        return v___x_4217_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0___boxed(
    mut v_f_4220_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_4221_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_4222_: *mut crate::leanh::LeanObject,
    mut v_a_u2083_4223_: *mut crate::leanh::LeanObject,
    mut v___y_4224_: *mut crate::leanh::LeanObject,
    mut v___y_4225_: *mut crate::leanh::LeanObject,
    mut v___y_4226_: *mut crate::leanh::LeanObject,
    mut v___y_4227_: *mut crate::leanh::LeanObject,
    mut v___y_4228_: *mut crate::leanh::LeanObject,
    mut v___y_4229_: *mut crate::leanh::LeanObject,
    mut v___y_4230_: *mut crate::leanh::LeanObject,
    mut v___y_4231_: *mut crate::leanh::LeanObject,
    mut v___y_4232_: *mut crate::leanh::LeanObject,
    mut v___y_4233_: *mut crate::leanh::LeanObject,
    mut v___y_4234_: *mut crate::leanh::LeanObject,
    mut v___y_4235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4236_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_f_4220_, v_a_u2081_4221_, v_a_u2082_4222_, v_a_u2083_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
    crate::leanh::lean_dec(v___y_4234_);
    crate::leanh::lean_dec_ref(v___y_4233_);
    crate::leanh::lean_dec(v___y_4232_);
    crate::leanh::lean_dec_ref(v___y_4231_);
    crate::leanh::lean_dec(v___y_4230_);
    crate::leanh::lean_dec_ref(v___y_4229_);
    crate::leanh::lean_dec(v___y_4228_);
    crate::leanh::lean_dec_ref(v___y_4227_);
    crate::leanh::lean_dec(v___y_4226_);
    crate::leanh::lean_dec(v___y_4225_);
    crate::leanh::lean_dec_ref(v___y_4224_);
    return v_res_4236_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(
    mut v_goal_4237_: *mut crate::leanh::LeanObject,
    mut v_ent_4238_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_4239_: *mut crate::leanh::LeanObject,
    mut v_H_4240_: *mut crate::leanh::LeanObject,
    mut v_T_4241_: *mut crate::leanh::LeanObject,
    mut v_a_4242_: *mut crate::leanh::LeanObject,
    mut v_a_4243_: *mut crate::leanh::LeanObject,
    mut v_a_4244_: *mut crate::leanh::LeanObject,
    mut v_a_4245_: *mut crate::leanh::LeanObject,
    mut v_a_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
    mut v_a_4249_: *mut crate::leanh::LeanObject,
    mut v_a_4250_: *mut crate::leanh::LeanObject,
    mut v_a_4251_: *mut crate::leanh::LeanObject,
    mut v_a_4252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4260_: u8 = 0;
    let mut v___y_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4270_: u8 = 0;
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4275_: u8 = 0;
    let mut v_a_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4279_: u8 = 0;
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut v_a_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut v___y_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_a_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut v_a_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4313_: u8 = 0;
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_H_4240_);
                v___x_4254_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(
                    v_H_4240_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_,
                );
                if crate::leanh::lean_obj_tag(v___x_4254_) == 0 {
                    v_a_4255_ = crate::leanh::lean_ctor_get(v___x_4254_, 0);
                    crate::leanh::lean_inc(v_a_4255_);
                    crate::leanh::lean_dec_ref_known(v___x_4254_, 1);
                    crate::leanh::lean_inc_ref(v_T_4241_);
                    v___x_4256_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(
                        v_T_4241_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4256_) == 0 {
                        v_a_4257_ = crate::leanh::lean_ctor_get(v___x_4256_, 0);
                        v_isSharedCheck_4301_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4256_)) as u8;
                        if v_isSharedCheck_4301_ == 0 {
                            v___x_4259_ = v___x_4256_;
                            v_isShared_4260_ = v_isSharedCheck_4301_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4257_);
                            crate::leanh::lean_dec(v___x_4256_);
                            v___x_4259_ = crate::leanh::lean_box(0);
                            v_isShared_4260_ = v_isSharedCheck_4301_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4255_);
                        crate::leanh::lean_dec_ref(v_T_4241_);
                        crate::leanh::lean_dec_ref(v_H_4240_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4239_);
                        crate::leanh::lean_dec_ref(v_ent_4238_);
                        crate::leanh::lean_dec(v_goal_4237_);
                        v_a_4302_ = crate::leanh::lean_ctor_get(v___x_4256_, 0);
                        v_isSharedCheck_4309_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4256_)) as u8;
                        if v_isSharedCheck_4309_ == 0 {
                            v___x_4304_ = v___x_4256_;
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4302_);
                            crate::leanh::lean_dec(v___x_4256_);
                            v___x_4304_ = crate::leanh::lean_box(0);
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_T_4241_);
                    crate::leanh::lean_dec_ref(v_H_4240_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4239_);
                    crate::leanh::lean_dec_ref(v_ent_4238_);
                    crate::leanh::lean_dec(v_goal_4237_);
                    v_a_4310_ = crate::leanh::lean_ctor_get(v___x_4254_, 0);
                    v_isSharedCheck_4317_ = (!crate::leanh::lean_is_exclusive(v___x_4254_)) as u8;
                    if v_isSharedCheck_4317_ == 0 {
                        v___x_4312_ = v___x_4254_;
                        v_isShared_4313_ = v_isSharedCheck_4317_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4310_);
                        crate::leanh::lean_dec(v___x_4254_);
                        v___x_4312_ = crate::leanh::lean_box(0);
                        v_isShared_4313_ = v_isSharedCheck_4317_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4255_) == 0 {
                    if crate::leanh::lean_obj_tag(v_a_4257_) == 0 {
                        crate::leanh::lean_dec_ref(v_T_4241_);
                        crate::leanh::lean_dec_ref(v_H_4240_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4239_);
                        crate::leanh::lean_dec_ref(v_ent_4238_);
                        crate::leanh::lean_dec(v_goal_4237_);
                        v___x_4297_ = crate::leanh::lean_box(0);
                        if v_isShared_4260_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4259_, 0, v___x_4297_);
                            v___x_4299_ = v___x_4259_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_4300_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
                            v___x_4299_ = v_reuseFailAlloc_4300_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4259_);
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4259_);
                    state = 10;
                    continue;
                }
            }
            2 => {
                v___x_4264_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_4238_, v_00_u03c3s_4239_, v___y_4262_, v___y_4263_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
                if crate::leanh::lean_obj_tag(v___x_4264_) == 0 {
                    v_a_4265_ = crate::leanh::lean_ctor_get(v___x_4264_, 0);
                    crate::leanh::lean_inc(v_a_4265_);
                    crate::leanh::lean_dec_ref_known(v___x_4264_, 1);
                    v___x_4266_ = l_Lean_MVarId_replaceTargetDefEq(
                        v_goal_4237_,
                        v_a_4265_,
                        v_a_4249_,
                        v_a_4250_,
                        v_a_4251_,
                        v_a_4252_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4266_) == 0 {
                        v_a_4267_ = crate::leanh::lean_ctor_get(v___x_4266_, 0);
                        v_isSharedCheck_4275_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4266_)) as u8;
                        if v_isSharedCheck_4275_ == 0 {
                            v___x_4269_ = v___x_4266_;
                            v_isShared_4270_ = v_isSharedCheck_4275_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4267_);
                            crate::leanh::lean_dec(v___x_4266_);
                            v___x_4269_ = crate::leanh::lean_box(0);
                            v_isShared_4270_ = v_isSharedCheck_4275_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4276_ = crate::leanh::lean_ctor_get(v___x_4266_, 0);
                        v_isSharedCheck_4283_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4266_)) as u8;
                        if v_isSharedCheck_4283_ == 0 {
                            v___x_4278_ = v___x_4266_;
                            v_isShared_4279_ = v_isSharedCheck_4283_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4276_);
                            crate::leanh::lean_dec(v___x_4266_);
                            v___x_4278_ = crate::leanh::lean_box(0);
                            v_isShared_4279_ = v_isSharedCheck_4283_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_4237_);
                    v_a_4284_ = crate::leanh::lean_ctor_get(v___x_4264_, 0);
                    v_isSharedCheck_4291_ = (!crate::leanh::lean_is_exclusive(v___x_4264_)) as u8;
                    if v_isSharedCheck_4291_ == 0 {
                        v___x_4286_ = v___x_4264_;
                        v_isShared_4287_ = v_isSharedCheck_4291_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4284_);
                        crate::leanh::lean_dec(v___x_4264_);
                        v___x_4286_ = crate::leanh::lean_box(0);
                        v_isShared_4287_ = v_isSharedCheck_4291_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4271_, 0, v_a_4267_);
                if v_isShared_4270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4269_, 0, v___x_4271_);
                    v___x_4273_ = v___x_4269_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
                    v___x_4273_ = v_reuseFailAlloc_4274_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4273_;
            }
            5 => {
                if v_isShared_4279_ == 0 {
                    v___x_4281_ = v___x_4278_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
                    v___x_4281_ = v_reuseFailAlloc_4282_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4281_;
            }
            7 => {
                if v_isShared_4287_ == 0 {
                    v___x_4289_ = v___x_4286_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4289_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_a_4257_) == 0 {
                    v___y_4262_ = v___y_4293_;
                    v___y_4263_ = v_T_4241_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_T_4241_);
                    v_val_4294_ = crate::leanh::lean_ctor_get(v_a_4257_, 0);
                    crate::leanh::lean_inc(v_val_4294_);
                    crate::leanh::lean_dec_ref_known(v_a_4257_, 1);
                    v___y_4262_ = v___y_4293_;
                    v___y_4263_ = v_val_4294_;
                    state = 2;
                    continue;
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_a_4255_) == 0 {
                    v___y_4293_ = v_H_4240_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_H_4240_);
                    v_val_4296_ = crate::leanh::lean_ctor_get(v_a_4255_, 0);
                    crate::leanh::lean_inc(v_val_4296_);
                    crate::leanh::lean_dec_ref_known(v_a_4255_, 1);
                    v___y_4293_ = v_val_4296_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                return v___x_4299_;
            }
            12 => {
                if v_isShared_4305_ == 0 {
                    v___x_4307_ = v___x_4304_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
                    v___x_4307_ = v_reuseFailAlloc_4308_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4307_;
            }
            14 => {
                if v_isShared_4313_ == 0 {
                    v___x_4315_ = v___x_4312_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4316_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
                    v___x_4315_ = v_reuseFailAlloc_4316_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_goal_4318_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_ent_4319_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3s_4320_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_H_4321_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_T_4322_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_4323_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_4324_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_4325_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_4326_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_4327_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_4328_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_4329_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_4330_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_4331_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_4332_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_4333_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_4334_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4335_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(v_goal_4318_, v_ent_4319_, v_00_u03c3s_4320_, v_H_4321_, v_T_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_);
    crate::leanh::lean_dec(v_a_4333_);
    crate::leanh::lean_dec_ref(v_a_4332_);
    crate::leanh::lean_dec(v_a_4331_);
    crate::leanh::lean_dec_ref(v_a_4330_);
    crate::leanh::lean_dec(v_a_4329_);
    crate::leanh::lean_dec_ref(v_a_4328_);
    crate::leanh::lean_dec(v_a_4327_);
    crate::leanh::lean_dec_ref(v_a_4326_);
    crate::leanh::lean_dec(v_a_4325_);
    crate::leanh::lean_dec(v_a_4324_);
    crate::leanh::lean_dec_ref(v_a_4323_);
    return v_res_4335_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1(
    mut v_f_4336_: *mut crate::leanh::LeanObject,
    mut v_a_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
    mut v___y_4341_: *mut crate::leanh::LeanObject,
    mut v___y_4342_: *mut crate::leanh::LeanObject,
    mut v___y_4343_: *mut crate::leanh::LeanObject,
    mut v___y_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
    mut v___y_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
    mut v___y_4348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4350_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_4336_, v_a_4337_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
    return v___x_4350_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___boxed(
    mut v_f_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
    mut v___y_4353_: *mut crate::leanh::LeanObject,
    mut v___y_4354_: *mut crate::leanh::LeanObject,
    mut v___y_4355_: *mut crate::leanh::LeanObject,
    mut v___y_4356_: *mut crate::leanh::LeanObject,
    mut v___y_4357_: *mut crate::leanh::LeanObject,
    mut v___y_4358_: *mut crate::leanh::LeanObject,
    mut v___y_4359_: *mut crate::leanh::LeanObject,
    mut v___y_4360_: *mut crate::leanh::LeanObject,
    mut v___y_4361_: *mut crate::leanh::LeanObject,
    mut v___y_4362_: *mut crate::leanh::LeanObject,
    mut v___y_4363_: *mut crate::leanh::LeanObject,
    mut v___y_4364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4365_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1(v_f_4351_, v_a_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
    crate::leanh::lean_dec(v___y_4363_);
    crate::leanh::lean_dec_ref(v___y_4362_);
    crate::leanh::lean_dec(v___y_4361_);
    crate::leanh::lean_dec_ref(v___y_4360_);
    crate::leanh::lean_dec(v___y_4359_);
    crate::leanh::lean_dec_ref(v___y_4358_);
    crate::leanh::lean_dec(v___y_4357_);
    crate::leanh::lean_dec_ref(v___y_4356_);
    crate::leanh::lean_dec(v___y_4355_);
    crate::leanh::lean_dec(v___y_4354_);
    crate::leanh::lean_dec_ref(v___y_4353_);
    return v_res_4365_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_4366_: *mut crate::leanh::LeanObject,
    mut v_x_4367_: *mut crate::leanh::LeanObject,
    mut v_x_4368_: *mut crate::leanh::LeanObject,
    mut v_x_4369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: u8 = 0;
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: u8 = 0;
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4370_ = crate::leanh::lean_ctor_get(v_x_4366_, 0);
                v_vs_4371_ = crate::leanh::lean_ctor_get(v_x_4366_, 1);
                v_isSharedCheck_4395_ = (!crate::leanh::lean_is_exclusive(v_x_4366_)) as u8;
                if v_isSharedCheck_4395_ == 0 {
                    v___x_4373_ = v_x_4366_;
                    v_isShared_4374_ = v_isSharedCheck_4395_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4371_);
                    crate::leanh::lean_inc(v_ks_4370_);
                    crate::leanh::lean_dec(v_x_4366_);
                    v___x_4373_ = crate::leanh::lean_box(0);
                    v_isShared_4374_ = v_isSharedCheck_4395_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4375_ = lean_array_get_size(v_ks_4370_);
                v___x_4376_ = lean_nat_dec_lt(v_x_4367_, v___x_4375_);
                if v___x_4376_ == 0 {
                    crate::leanh::lean_dec(v_x_4367_);
                    v___x_4377_ = lean_array_push(v_ks_4370_, v_x_4368_);
                    v___x_4378_ = lean_array_push(v_vs_4371_, v_x_4369_);
                    if v_isShared_4374_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4373_, 1, v___x_4378_);
                        crate::leanh::lean_ctor_set(v___x_4373_, 0, v___x_4377_);
                        v___x_4380_ = v___x_4373_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4381_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4377_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 1, v___x_4378_);
                        v___x_4380_ = v_reuseFailAlloc_4381_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4382_ = lean_array_fget_borrowed(v_ks_4370_, v_x_4367_);
                    v___x_4383_ = l_Lean_instBEqMVarId_beq(v_x_4368_, v_k_x27_4382_);
                    if v___x_4383_ == 0 {
                        if v_isShared_4374_ == 0 {
                            v___x_4385_ = v___x_4373_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4389_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_ks_4370_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 1, v_vs_4371_);
                            v___x_4385_ = v_reuseFailAlloc_4389_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4390_ = lean_array_fset(v_ks_4370_, v_x_4367_, v_x_4368_);
                        v___x_4391_ = lean_array_fset(v_vs_4371_, v_x_4367_, v_x_4369_);
                        crate::leanh::lean_dec(v_x_4367_);
                        if v_isShared_4374_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4373_, 1, v___x_4391_);
                            crate::leanh::lean_ctor_set(v___x_4373_, 0, v___x_4390_);
                            v___x_4393_ = v___x_4373_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4394_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4390_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4394_, 1, v___x_4391_);
                            v___x_4393_ = v_reuseFailAlloc_4394_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4380_;
            }
            3 => {
                v___x_4386_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4387_ = lean_nat_add(v_x_4367_, v___x_4386_);
                crate::leanh::lean_dec(v_x_4367_);
                v_x_4366_ = v___x_4385_;
                v_x_4367_ = v___x_4387_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4393_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_4396_: *mut crate::leanh::LeanObject,
    mut v_k_4397_: *mut crate::leanh::LeanObject,
    mut v_v_4398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4399_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4400_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_4396_, v___x_4399_, v_k_4397_, v_v_4398_);
    return v___x_4400_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_4401_: usize = 0;
    let mut v___x_4402_: usize = 0;
    let mut v___x_4403_: usize = 0;
    v___x_4401_ = 5usize;
    v___x_4402_ = 1usize;
    v___x_4403_ = lean_usize_shift_left(v___x_4402_, v___x_4401_);
    return v___x_4403_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_4404_: usize = 0;
    let mut v___x_4405_: usize = 0;
    let mut v___x_4406_: usize = 0;
    v___x_4404_ = 1usize;
    v___x_4405_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_4406_ = lean_usize_sub(v___x_4405_, v___x_4404_);
    return v___x_4406_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4407_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4407_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg(
    mut v_x_4408_: *mut crate::leanh::LeanObject,
    mut v_x_4409_: usize,
    mut v_x_4410_: usize,
    mut v_x_4411_: *mut crate::leanh::LeanObject,
    mut v_x_4412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: usize = 0;
    let mut v___x_4415_: usize = 0;
    let mut v___x_4416_: usize = 0;
    let mut v___x_4417_: usize = 0;
    let mut v_j_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: u8 = 0;
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4423_: u8 = 0;
    let mut v_v_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4437_: u8 = 0;
    let mut v___x_4438_: u8 = 0;
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4444_: u8 = 0;
    let mut v_node_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4448_: u8 = 0;
    let mut v___x_4449_: usize = 0;
    let mut v___x_4450_: usize = 0;
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4455_: u8 = 0;
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut v_unused_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4468_: u8 = 0;
    let mut v_ks_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: usize = 0;
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: u8 = 0;
    let mut v_reuseFailAlloc_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4408_) == 0 {
                    v_es_4413_ = crate::leanh::lean_ctor_get(v_x_4408_, 0);
                    v___x_4414_ = 5usize;
                    v___x_4415_ = 1usize;
                    v___x_4416_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4417_ = lean_usize_land(v_x_4409_, v___x_4416_);
                    v_j_4418_ = lean_usize_to_nat(v___x_4417_);
                    v___x_4419_ = lean_array_get_size(v_es_4413_);
                    v___x_4420_ = lean_nat_dec_lt(v_j_4418_, v___x_4419_);
                    if v___x_4420_ == 0 {
                        crate::leanh::lean_dec(v_j_4418_);
                        crate::leanh::lean_dec(v_x_4412_);
                        crate::leanh::lean_dec(v_x_4411_);
                        return v_x_4408_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4413_);
                        v_isSharedCheck_4457_ = (!crate::leanh::lean_is_exclusive(v_x_4408_)) as u8;
                        if v_isSharedCheck_4457_ == 0 {
                            v_unused_4458_ = crate::leanh::lean_ctor_get(v_x_4408_, 0);
                            crate::leanh::lean_dec(v_unused_4458_);
                            v___x_4422_ = v_x_4408_;
                            v_isShared_4423_ = v_isSharedCheck_4457_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4408_);
                            v___x_4422_ = crate::leanh::lean_box(0);
                            v_isShared_4423_ = v_isSharedCheck_4457_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4459_ = crate::leanh::lean_ctor_get(v_x_4408_, 0);
                    v_vs_4460_ = crate::leanh::lean_ctor_get(v_x_4408_, 1);
                    v_isSharedCheck_4480_ = (!crate::leanh::lean_is_exclusive(v_x_4408_)) as u8;
                    if v_isSharedCheck_4480_ == 0 {
                        v___x_4462_ = v_x_4408_;
                        v_isShared_4463_ = v_isSharedCheck_4480_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4460_);
                        crate::leanh::lean_inc(v_ks_4459_);
                        crate::leanh::lean_dec(v_x_4408_);
                        v___x_4462_ = crate::leanh::lean_box(0);
                        v_isShared_4463_ = v_isSharedCheck_4480_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4424_ = lean_array_fget(v_es_4413_, v_j_4418_);
                v___x_4425_ = crate::leanh::lean_box(0);
                v_xs_x27_4426_ = lean_array_fset(v_es_4413_, v_j_4418_, v___x_4425_);
                match crate::leanh::lean_obj_tag(v_v_4424_) {
                    0 => {
                        v_key_4433_ = crate::leanh::lean_ctor_get(v_v_4424_, 0);
                        v_val_4434_ = crate::leanh::lean_ctor_get(v_v_4424_, 1);
                        v_isSharedCheck_4444_ = (!crate::leanh::lean_is_exclusive(v_v_4424_)) as u8;
                        if v_isSharedCheck_4444_ == 0 {
                            v___x_4436_ = v_v_4424_;
                            v_isShared_4437_ = v_isSharedCheck_4444_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4434_);
                            crate::leanh::lean_inc(v_key_4433_);
                            crate::leanh::lean_dec(v_v_4424_);
                            v___x_4436_ = crate::leanh::lean_box(0);
                            v_isShared_4437_ = v_isSharedCheck_4444_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4445_ = crate::leanh::lean_ctor_get(v_v_4424_, 0);
                        v_isSharedCheck_4455_ = (!crate::leanh::lean_is_exclusive(v_v_4424_)) as u8;
                        if v_isSharedCheck_4455_ == 0 {
                            v___x_4447_ = v_v_4424_;
                            v_isShared_4448_ = v_isSharedCheck_4455_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4445_);
                            crate::leanh::lean_dec(v_v_4424_);
                            v___x_4447_ = crate::leanh::lean_box(0);
                            v_isShared_4448_ = v_isSharedCheck_4455_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4456_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4456_, 0, v_x_4411_);
                        crate::leanh::lean_ctor_set(v___x_4456_, 1, v_x_4412_);
                        v___y_4428_ = v___x_4456_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4429_ = lean_array_fset(v_xs_x27_4426_, v_j_4418_, v___y_4428_);
                crate::leanh::lean_dec(v_j_4418_);
                if v_isShared_4423_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4422_, 0, v___x_4429_);
                    v___x_4431_ = v___x_4422_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4432_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4429_);
                    v___x_4431_ = v_reuseFailAlloc_4432_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4431_;
            }
            4 => {
                v___x_4438_ = l_Lean_instBEqMVarId_beq(v_x_4411_, v_key_4433_);
                if v___x_4438_ == 0 {
                    crate::leanh::lean_del_object(v___x_4436_);
                    v___x_4439_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4433_,
                        v_val_4434_,
                        v_x_4411_,
                        v_x_4412_,
                    );
                    v___x_4440_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4440_, 0, v___x_4439_);
                    v___y_4428_ = v___x_4440_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4434_);
                    crate::leanh::lean_dec(v_key_4433_);
                    if v_isShared_4437_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4436_, 1, v_x_4412_);
                        crate::leanh::lean_ctor_set(v___x_4436_, 0, v_x_4411_);
                        v___x_4442_ = v___x_4436_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4443_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_x_4411_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4443_, 1, v_x_4412_);
                        v___x_4442_ = v_reuseFailAlloc_4443_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4428_ = v___x_4442_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4449_ = lean_usize_shift_right(v_x_4409_, v___x_4414_);
                v___x_4450_ = lean_usize_add(v_x_4410_, v___x_4415_);
                v___x_4451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg(v_node_4445_, v___x_4449_, v___x_4450_, v_x_4411_, v_x_4412_);
                if v_isShared_4448_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4447_, 0, v___x_4451_);
                    v___x_4453_ = v___x_4447_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4451_);
                    v___x_4453_ = v_reuseFailAlloc_4454_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4428_ = v___x_4453_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4463_ == 0 {
                    v___x_4465_ = v___x_4462_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4479_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_ks_4459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_vs_4460_);
                    v___x_4465_ = v_reuseFailAlloc_4479_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4466_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2___redArg(v___x_4465_, v_x_4411_, v_x_4412_);
                v___x_4474_ = 7usize;
                v___x_4475_ = lean_usize_dec_le(v___x_4474_, v_x_4410_);
                if v___x_4475_ == 0 {
                    v___x_4476_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4466_);
                    v___x_4477_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4478_ = lean_nat_dec_lt(v___x_4476_, v___x_4477_);
                    crate::leanh::lean_dec(v___x_4476_);
                    v___y_4468_ = v___x_4478_;
                    state = 10;
                    continue;
                } else {
                    v___y_4468_ = v___x_4475_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4468_ == 0 {
                    v_ks_4469_ = crate::leanh::lean_ctor_get(v_newNode_4466_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4469_);
                    v_vs_4470_ = crate::leanh::lean_ctor_get(v_newNode_4466_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4470_);
                    crate::leanh::lean_dec_ref(v_newNode_4466_);
                    v___x_4471_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4472_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_4473_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4410_, v_ks_4469_, v_vs_4470_, v___x_4471_, v___x_4472_);
                    crate::leanh::lean_dec_ref(v_vs_4470_);
                    crate::leanh::lean_dec_ref(v_ks_4469_);
                    return v___x_4473_;
                } else {
                    return v_newNode_4466_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_4481_: usize,
    mut v_keys_4482_: *mut crate::leanh::LeanObject,
    mut v_vals_4483_: *mut crate::leanh::LeanObject,
    mut v_i_4484_: *mut crate::leanh::LeanObject,
    mut v_entries_4485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: u8 = 0;
    let mut v_k_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: u64 = 0;
    let mut v_h_4491_: usize = 0;
    let mut v___x_4492_: usize = 0;
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: usize = 0;
    let mut v___x_4495_: usize = 0;
    let mut v___x_4496_: usize = 0;
    let mut v_h_4497_: usize = 0;
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4486_ = lean_array_get_size(v_keys_4482_);
                v___x_4487_ = lean_nat_dec_lt(v_i_4484_, v___x_4486_);
                if v___x_4487_ == 0 {
                    crate::leanh::lean_dec(v_i_4484_);
                    return v_entries_4485_;
                } else {
                    v_k_4488_ = lean_array_fget_borrowed(v_keys_4482_, v_i_4484_);
                    v_v_4489_ = lean_array_fget_borrowed(v_vals_4483_, v_i_4484_);
                    v___x_4490_ = l_Lean_instHashableMVarId_hash(v_k_4488_);
                    v_h_4491_ = lean_uint64_to_usize(v___x_4490_);
                    v___x_4492_ = 5usize;
                    v___x_4493_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4494_ = 1usize;
                    v___x_4495_ = lean_usize_sub(v_depth_4481_, v___x_4494_);
                    v___x_4496_ = lean_usize_mul(v___x_4492_, v___x_4495_);
                    v_h_4497_ = lean_usize_shift_right(v_h_4491_, v___x_4496_);
                    v___x_4498_ = lean_nat_add(v_i_4484_, v___x_4493_);
                    crate::leanh::lean_dec(v_i_4484_);
                    crate::leanh::lean_inc(v_v_4489_);
                    crate::leanh::lean_inc(v_k_4488_);
                    v___x_4499_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg(v_entries_4485_, v_h_4497_, v_depth_4481_, v_k_4488_, v_v_4489_);
                    v_i_4484_ = v___x_4498_;
                    v_entries_4485_ = v___x_4499_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_4501_: *mut crate::leanh::LeanObject,
    mut v_keys_4502_: *mut crate::leanh::LeanObject,
    mut v_vals_4503_: *mut crate::leanh::LeanObject,
    mut v_i_4504_: *mut crate::leanh::LeanObject,
    mut v_entries_4505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4506_: usize = 0;
    let mut v_res_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4506_ = crate::leanh::lean_unbox_usize(v_depth_4501_);
    crate::leanh::lean_dec(v_depth_4501_);
    v_res_4507_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_4506_, v_keys_4502_, v_vals_4503_, v_i_4504_, v_entries_4505_);
    crate::leanh::lean_dec_ref(v_vals_4503_);
    crate::leanh::lean_dec_ref(v_keys_4502_);
    return v_res_4507_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4508_: *mut crate::leanh::LeanObject,
    mut v_x_4509_: *mut crate::leanh::LeanObject,
    mut v_x_4510_: *mut crate::leanh::LeanObject,
    mut v_x_4511_: *mut crate::leanh::LeanObject,
    mut v_x_4512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_28835__boxed_4513_: usize = 0;
    let mut v_x_28836__boxed_4514_: usize = 0;
    let mut v_res_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_28835__boxed_4513_ = crate::leanh::lean_unbox_usize(v_x_4509_);
    crate::leanh::lean_dec(v_x_4509_);
    v_x_28836__boxed_4514_ = crate::leanh::lean_unbox_usize(v_x_4510_);
    crate::leanh::lean_dec(v_x_4510_);
    v_res_4515_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg(v_x_4508_, v_x_28835__boxed_4513_, v_x_28836__boxed_4514_, v_x_4511_, v_x_4512_);
    return v_res_4515_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0___redArg(
    mut v_x_4516_: *mut crate::leanh::LeanObject,
    mut v_x_4517_: *mut crate::leanh::LeanObject,
    mut v_x_4518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4519_: u64 = 0;
    let mut v___x_4520_: usize = 0;
    let mut v___x_4521_: usize = 0;
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4519_ = l_Lean_instHashableMVarId_hash(v_x_4517_);
    v___x_4520_ = lean_uint64_to_usize(v___x_4519_);
    v___x_4521_ = 1usize;
    v___x_4522_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg(v_x_4516_, v___x_4520_, v___x_4521_, v_x_4517_, v_x_4518_);
    return v___x_4522_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___redArg(
    mut v_mvarId_4523_: *mut crate::leanh::LeanObject,
    mut v_val_4524_: *mut crate::leanh::LeanObject,
    mut v___y_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4535_: u8 = 0;
    let mut v_depth_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4548_: u8 = 0;
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut v_isSharedCheck_4560_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4527_ = lean_st_ref_take(v___y_4525_);
                v_mctx_4528_ = crate::leanh::lean_ctor_get(v___x_4527_, 0);
                v_cache_4529_ = crate::leanh::lean_ctor_get(v___x_4527_, 1);
                v_zetaDeltaFVarIds_4530_ = crate::leanh::lean_ctor_get(v___x_4527_, 2);
                v_postponed_4531_ = crate::leanh::lean_ctor_get(v___x_4527_, 3);
                v_diag_4532_ = crate::leanh::lean_ctor_get(v___x_4527_, 4);
                v_isSharedCheck_4560_ = (!crate::leanh::lean_is_exclusive(v___x_4527_)) as u8;
                if v_isSharedCheck_4560_ == 0 {
                    v___x_4534_ = v___x_4527_;
                    v_isShared_4535_ = v_isSharedCheck_4560_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4532_);
                    crate::leanh::lean_inc(v_postponed_4531_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4530_);
                    crate::leanh::lean_inc(v_cache_4529_);
                    crate::leanh::lean_inc(v_mctx_4528_);
                    crate::leanh::lean_dec(v___x_4527_);
                    v___x_4534_ = crate::leanh::lean_box(0);
                    v_isShared_4535_ = v_isSharedCheck_4560_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4536_ = crate::leanh::lean_ctor_get(v_mctx_4528_, 0);
                v_levelAssignDepth_4537_ = crate::leanh::lean_ctor_get(v_mctx_4528_, 1);
                v_lmvarCounter_4538_ = crate::leanh::lean_ctor_get(v_mctx_4528_, 2);
                v_mvarCounter_4539_ = crate::leanh::lean_ctor_get(v_mctx_4528_, 3);
                v_lDecls_4540_ = crate::leanh::lean_ctor_get(v_mctx_4528_, 4);
                v_decls_4541_ = crate::leanh::lean_ctor_get(v_mctx_4528_, 5);
                v_userNames_4542_ = crate::leanh::lean_ctor_get(v_mctx_4528_, 6);
                v_lAssignment_4543_ = crate::leanh::lean_ctor_get(v_mctx_4528_, 7);
                v_eAssignment_4544_ = crate::leanh::lean_ctor_get(v_mctx_4528_, 8);
                v_dAssignment_4545_ = crate::leanh::lean_ctor_get(v_mctx_4528_, 9);
                v_isSharedCheck_4559_ = (!crate::leanh::lean_is_exclusive(v_mctx_4528_)) as u8;
                if v_isSharedCheck_4559_ == 0 {
                    v___x_4547_ = v_mctx_4528_;
                    v_isShared_4548_ = v_isSharedCheck_4559_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_4545_);
                    crate::leanh::lean_inc(v_eAssignment_4544_);
                    crate::leanh::lean_inc(v_lAssignment_4543_);
                    crate::leanh::lean_inc(v_userNames_4542_);
                    crate::leanh::lean_inc(v_decls_4541_);
                    crate::leanh::lean_inc(v_lDecls_4540_);
                    crate::leanh::lean_inc(v_mvarCounter_4539_);
                    crate::leanh::lean_inc(v_lmvarCounter_4538_);
                    crate::leanh::lean_inc(v_levelAssignDepth_4537_);
                    crate::leanh::lean_inc(v_depth_4536_);
                    crate::leanh::lean_dec(v_mctx_4528_);
                    v___x_4547_ = crate::leanh::lean_box(0);
                    v_isShared_4548_ = v_isSharedCheck_4559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4549_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0___redArg(v_eAssignment_4544_, v_mvarId_4523_, v_val_4524_);
                if v_isShared_4548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4547_, 8, v___x_4549_);
                    v___x_4551_ = v___x_4547_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_depth_4536_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4558_,
                        1,
                        v_levelAssignDepth_4537_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 2, v_lmvarCounter_4538_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 3, v_mvarCounter_4539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 4, v_lDecls_4540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 5, v_decls_4541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 6, v_userNames_4542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 7, v_lAssignment_4543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 8, v___x_4549_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 9, v_dAssignment_4545_);
                    v___x_4551_ = v_reuseFailAlloc_4558_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4535_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4534_, 0, v___x_4551_);
                    v___x_4553_ = v___x_4534_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4557_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4551_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_cache_4529_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4557_,
                        2,
                        v_zetaDeltaFVarIds_4530_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 3, v_postponed_4531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 4, v_diag_4532_);
                    v___x_4553_ = v_reuseFailAlloc_4557_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4554_ = lean_st_ref_set(v___y_4525_, v___x_4553_);
                v___x_4555_ = crate::leanh::lean_box(0);
                v___x_4556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4556_, 0, v___x_4555_);
                return v___x_4556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___redArg___boxed(
    mut v_mvarId_4561_: *mut crate::leanh::LeanObject,
    mut v_val_4562_: *mut crate::leanh::LeanObject,
    mut v___y_4563_: *mut crate::leanh::LeanObject,
    mut v___y_4564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4565_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___redArg(v_mvarId_4561_, v_val_4562_, v___y_4563_);
    crate::leanh::lean_dec(v___y_4563_);
    return v_res_4565_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4575_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__3;
    v___x_4576_ = l_Lean_stringToMessageData(v___x_4575_);
    return v___x_4576_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4580_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__6;
    v___x_4581_ = l_Lean_stringToMessageData(v___x_4580_);
    return v___x_4581_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails(
    mut v_goal_4582_: *mut crate::leanh::LeanObject,
    mut v_ent_4583_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_4584_: *mut crate::leanh::LeanObject,
    mut v_H_4585_: *mut crate::leanh::LeanObject,
    mut v_T_4586_: *mut crate::leanh::LeanObject,
    mut v_a_4587_: *mut crate::leanh::LeanObject,
    mut v_a_4588_: *mut crate::leanh::LeanObject,
    mut v_a_4589_: *mut crate::leanh::LeanObject,
    mut v_a_4590_: *mut crate::leanh::LeanObject,
    mut v_a_4591_: *mut crate::leanh::LeanObject,
    mut v_a_4592_: *mut crate::leanh::LeanObject,
    mut v_a_4593_: *mut crate::leanh::LeanObject,
    mut v_a_4594_: *mut crate::leanh::LeanObject,
    mut v_a_4595_: *mut crate::leanh::LeanObject,
    mut v_a_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4601_: u8 = 0;
    let mut v___y_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4627_: u8 = 0;
    let mut v_unused_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4643_: u8 = 0;
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4648_: u8 = 0;
    let mut v_val_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4652_: u8 = 0;
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4660_: u8 = 0;
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4665_: u8 = 0;
    let mut v_a_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4669_: u8 = 0;
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4673_: u8 = 0;
    let mut v_options_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4675_: u8 = 0;
    let mut v_inheritedTraceOptions_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: u8 = 0;
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4686_: u8 = 0;
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4690_: u8 = 0;
    let mut v___y_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4704_: u8 = 0;
    let mut v_ctxApprox_4705_: u8 = 0;
    let mut v_quasiPatternApprox_4706_: u8 = 0;
    let mut v_constApprox_4707_: u8 = 0;
    let mut v_isDefEqStuckEx_4708_: u8 = 0;
    let mut v_unificationHints_4709_: u8 = 0;
    let mut v_proofIrrelevance_4710_: u8 = 0;
    let mut v_offsetCnstrs_4711_: u8 = 0;
    let mut v_transparency_4712_: u8 = 0;
    let mut v_etaStruct_4713_: u8 = 0;
    let mut v_univApprox_4714_: u8 = 0;
    let mut v_iota_4715_: u8 = 0;
    let mut v_beta_4716_: u8 = 0;
    let mut v_proj_4717_: u8 = 0;
    let mut v_zeta_4718_: u8 = 0;
    let mut v_zetaDelta_4719_: u8 = 0;
    let mut v_zetaUnused_4720_: u8 = 0;
    let mut v_zetaHave_4721_: u8 = 0;
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4724_: u8 = 0;
    let mut v_trackZetaDelta_4725_: u8 = 0;
    let mut v_zetaDeltaSet_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4732_: u8 = 0;
    let mut v_inTypeClassResolution_4733_: u8 = 0;
    let mut v_cacheInferType_4734_: u8 = 0;
    let mut v___x_4735_: u8 = 0;
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: u64 = 0;
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: u8 = 0;
    let mut v_a_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: u8 = 0;
    let mut v_a_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4751_: u8 = 0;
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4755_: u8 = 0;
    let mut v_reuseFailAlloc_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4757_: u8 = 0;
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: u8 = 0;
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4767_: u8 = 0;
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4599_ = crate::leanh::lean_ctor_get(v_a_4596_, 2);
                v_inheritedTraceOptions_4600_ = crate::leanh::lean_ctor_get(v_a_4596_, 13);
                v_hasTrace_4601_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_4599_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_cls_4629_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                if v_hasTrace_4601_ == 0 {
                    v___y_4692_ = v_a_4587_;
                    v___y_4693_ = v_a_4588_;
                    v___y_4694_ = v_a_4589_;
                    v___y_4695_ = v_a_4590_;
                    v___y_4696_ = v_a_4591_;
                    v___y_4697_ = v_a_4592_;
                    v___y_4698_ = v_a_4593_;
                    v___y_4699_ = v_a_4594_;
                    v___y_4700_ = v_a_4595_;
                    v___y_4701_ = v_a_4596_;
                    v___y_4702_ = v_a_4597_;
                    state = 14;
                    continue;
                } else {
                    v___x_4758_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
                    v___x_4759_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4600_,
                        v_options_4599_,
                        v___x_4758_,
                    );
                    if v___x_4759_ == 0 {
                        v___y_4692_ = v_a_4587_;
                        v___y_4693_ = v_a_4588_;
                        v___y_4694_ = v_a_4589_;
                        v___y_4695_ = v_a_4590_;
                        v___y_4696_ = v_a_4591_;
                        v___y_4697_ = v_a_4592_;
                        v___y_4698_ = v_a_4593_;
                        v___y_4699_ = v_a_4594_;
                        v___y_4700_ = v_a_4595_;
                        v___y_4701_ = v_a_4596_;
                        v___y_4702_ = v_a_4597_;
                        state = 14;
                        continue;
                    } else {
                        v___x_4760_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7);
                        crate::leanh::lean_inc(v_goal_4582_);
                        v___x_4761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4761_, 0, v_goal_4582_);
                        v___x_4762_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4762_, 0, v___x_4760_);
                        crate::leanh::lean_ctor_set(v___x_4762_, 1, v___x_4761_);
                        v___x_4763_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_4629_, v___x_4762_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
                        if crate::leanh::lean_obj_tag(v___x_4763_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4763_, 1);
                            v___y_4692_ = v_a_4587_;
                            v___y_4693_ = v_a_4588_;
                            v___y_4694_ = v_a_4589_;
                            v___y_4695_ = v_a_4590_;
                            v___y_4696_ = v_a_4591_;
                            v___y_4697_ = v_a_4592_;
                            v___y_4698_ = v_a_4593_;
                            v___y_4699_ = v_a_4594_;
                            v___y_4700_ = v_a_4595_;
                            v___y_4701_ = v_a_4596_;
                            v___y_4702_ = v_a_4597_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_T_4586_);
                            crate::leanh::lean_dec_ref(v_H_4585_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_4584_);
                            crate::leanh::lean_dec(v_goal_4582_);
                            v_a_4764_ = crate::leanh::lean_ctor_get(v___x_4763_, 0);
                            v_isSharedCheck_4771_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4763_)) as u8;
                            if v_isSharedCheck_4771_ == 0 {
                                v___x_4766_ = v___x_4763_;
                                v_isShared_4767_ = v_isSharedCheck_4771_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4764_);
                                crate::leanh::lean_dec(v___x_4763_);
                                v___x_4766_ = crate::leanh::lean_box(0);
                                v_isShared_4767_ = v_isSharedCheck_4771_;
                                state = 19;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4615_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2;
                v___x_4616_ = l_Lean_Expr_constLevels_x21(v_ent_4583_);
                v___x_4617_ = l_Lean_mkConst(v___x_4615_, v___x_4616_);
                v___x_4618_ = l_Lean_mkAppB(v___x_4617_, v_00_u03c3s_4584_, v_H_4585_);
                v___x_4619_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___redArg(v_goal_4582_, v___x_4618_, v___y_4612_);
                v_isSharedCheck_4627_ = (!crate::leanh::lean_is_exclusive(v___x_4619_)) as u8;
                if v_isSharedCheck_4627_ == 0 {
                    v_unused_4628_ = crate::leanh::lean_ctor_get(v___x_4619_, 0);
                    crate::leanh::lean_dec(v_unused_4628_);
                    v___x_4621_ = v___x_4619_;
                    v_isShared_4622_ = v_isSharedCheck_4627_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4619_);
                    v___x_4621_ = crate::leanh::lean_box(0);
                    v_isShared_4622_ = v_isSharedCheck_4627_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_4603_);
                v___x_4623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4623_, 0, v___y_4603_);
                if v_isShared_4622_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4621_, 0, v___x_4623_);
                    v___x_4625_ = v___x_4621_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
                    v___x_4625_ = v_reuseFailAlloc_4626_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4625_;
            }
            4 => {
                if v_a_4643_ == 0 {
                    crate::leanh::lean_dec_ref(v_H_4585_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4584_);
                    v___x_4644_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails(
                        v_goal_4582_,
                        v___y_4632_,
                        v___y_4637_,
                        v___y_4641_,
                        v___y_4635_,
                        v___y_4640_,
                        v___y_4642_,
                        v___y_4638_,
                        v___y_4636_,
                        v___y_4633_,
                        v___y_4631_,
                        v___y_4634_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4644_) == 0 {
                        v_a_4645_ = crate::leanh::lean_ctor_get(v___x_4644_, 0);
                        v_isSharedCheck_4665_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4644_)) as u8;
                        if v_isSharedCheck_4665_ == 0 {
                            v___x_4647_ = v___x_4644_;
                            v_isShared_4648_ = v_isSharedCheck_4665_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4645_);
                            crate::leanh::lean_dec(v___x_4644_);
                            v___x_4647_ = crate::leanh::lean_box(0);
                            v_isShared_4648_ = v_isSharedCheck_4665_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_4666_ = crate::leanh::lean_ctor_get(v___x_4644_, 0);
                        v_isSharedCheck_4673_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4644_)) as u8;
                        if v_isSharedCheck_4673_ == 0 {
                            v___x_4668_ = v___x_4644_;
                            v_isShared_4669_ = v_isSharedCheck_4673_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4666_);
                            crate::leanh::lean_dec(v___x_4644_);
                            v___x_4668_ = crate::leanh::lean_box(0);
                            v_isShared_4669_ = v_isSharedCheck_4673_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v_options_4674_ = crate::leanh::lean_ctor_get(v___y_4631_, 2);
                    v_hasTrace_4675_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_4674_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4675_ == 0 {
                        v___y_4603_ = v___y_4639_;
                        v___y_4604_ = v___y_4632_;
                        v___y_4605_ = v___y_4637_;
                        v___y_4606_ = v___y_4641_;
                        v___y_4607_ = v___y_4635_;
                        v___y_4608_ = v___y_4640_;
                        v___y_4609_ = v___y_4642_;
                        v___y_4610_ = v___y_4638_;
                        v___y_4611_ = v___y_4636_;
                        v___y_4612_ = v___y_4633_;
                        v___y_4613_ = v___y_4631_;
                        v___y_4614_ = v___y_4634_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4676_ =
                            crate::leanh::lean_ctor_get(v___y_4631_, 13);
                        v___x_4677_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
                        v___x_4678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4676_,
                            v_options_4674_,
                            v___x_4677_,
                        );
                        if v___x_4678_ == 0 {
                            v___y_4603_ = v___y_4639_;
                            v___y_4604_ = v___y_4632_;
                            v___y_4605_ = v___y_4637_;
                            v___y_4606_ = v___y_4641_;
                            v___y_4607_ = v___y_4635_;
                            v___y_4608_ = v___y_4640_;
                            v___y_4609_ = v___y_4642_;
                            v___y_4610_ = v___y_4638_;
                            v___y_4611_ = v___y_4636_;
                            v___y_4612_ = v___y_4633_;
                            v___y_4613_ = v___y_4631_;
                            v___y_4614_ = v___y_4634_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4679_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4);
                            crate::leanh::lean_inc(v_goal_4582_);
                            v___x_4680_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4680_, 0, v_goal_4582_);
                            v___x_4681_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4681_, 0, v___x_4679_);
                            crate::leanh::lean_ctor_set(v___x_4681_, 1, v___x_4680_);
                            v___x_4682_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_4629_, v___x_4681_, v___y_4636_, v___y_4633_, v___y_4631_, v___y_4634_);
                            if crate::leanh::lean_obj_tag(v___x_4682_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4682_, 1);
                                v___y_4603_ = v___y_4639_;
                                v___y_4604_ = v___y_4632_;
                                v___y_4605_ = v___y_4637_;
                                v___y_4606_ = v___y_4641_;
                                v___y_4607_ = v___y_4635_;
                                v___y_4608_ = v___y_4640_;
                                v___y_4609_ = v___y_4642_;
                                v___y_4610_ = v___y_4638_;
                                v___y_4611_ = v___y_4636_;
                                v___y_4612_ = v___y_4633_;
                                v___y_4613_ = v___y_4631_;
                                v___y_4614_ = v___y_4634_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_H_4585_);
                                crate::leanh::lean_dec_ref(v_00_u03c3s_4584_);
                                crate::leanh::lean_dec(v_goal_4582_);
                                v_a_4683_ = crate::leanh::lean_ctor_get(v___x_4682_, 0);
                                v_isSharedCheck_4690_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4682_)) as u8;
                                if v_isSharedCheck_4690_ == 0 {
                                    v___x_4685_ = v___x_4682_;
                                    v_isShared_4686_ = v_isSharedCheck_4690_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4683_);
                                    crate::leanh::lean_dec(v___x_4682_);
                                    v___x_4685_ = crate::leanh::lean_box(0);
                                    v_isShared_4686_ = v_isSharedCheck_4690_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_4645_) == 1 {
                    v_val_4649_ = crate::leanh::lean_ctor_get(v_a_4645_, 0);
                    v_isSharedCheck_4660_ = (!crate::leanh::lean_is_exclusive(v_a_4645_)) as u8;
                    if v_isSharedCheck_4660_ == 0 {
                        v___x_4651_ = v_a_4645_;
                        v_isShared_4652_ = v_isSharedCheck_4660_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4649_);
                        crate::leanh::lean_dec(v_a_4645_);
                        v___x_4651_ = crate::leanh::lean_box(0);
                        v_isShared_4652_ = v_isSharedCheck_4660_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4645_);
                    v___x_4661_ = crate::leanh::lean_box(0);
                    if v_isShared_4648_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4647_, 0, v___x_4661_);
                        v___x_4663_ = v___x_4647_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4664_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4661_);
                        v___x_4663_ = v_reuseFailAlloc_4664_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc(v___y_4639_);
                v___x_4653_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4653_, 0, v_val_4649_);
                crate::leanh::lean_ctor_set(v___x_4653_, 1, v___y_4639_);
                if v_isShared_4652_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4651_, 0, v___x_4653_);
                    v___x_4655_ = v___x_4651_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4653_);
                    v___x_4655_ = v_reuseFailAlloc_4659_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4648_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4647_, 0, v___x_4655_);
                    v___x_4657_ = v___x_4647_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4658_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4655_);
                    v___x_4657_ = v_reuseFailAlloc_4658_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4657_;
            }
            9 => {
                return v___x_4663_;
            }
            10 => {
                if v_isShared_4669_ == 0 {
                    v___x_4671_ = v___x_4668_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4672_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
                    v___x_4671_ = v_reuseFailAlloc_4672_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4671_;
            }
            12 => {
                if v_isShared_4686_ == 0 {
                    v___x_4688_ = v___x_4685_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4689_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
                    v___x_4688_ = v_reuseFailAlloc_4689_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4688_;
            }
            14 => {
                v___x_4703_ = l_Lean_Meta_Context_config(v___y_4699_);
                v_foApprox_4704_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 0 as u32);
                v_ctxApprox_4705_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 1 as u32);
                v_quasiPatternApprox_4706_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_4703_, 2 as u32);
                v_constApprox_4707_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 3 as u32);
                v_isDefEqStuckEx_4708_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 4 as u32);
                v_unificationHints_4709_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 5 as u32);
                v_proofIrrelevance_4710_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 6 as u32);
                v_offsetCnstrs_4711_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 8 as u32);
                v_transparency_4712_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 9 as u32);
                v_etaStruct_4713_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 10 as u32);
                v_univApprox_4714_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 11 as u32);
                v_iota_4715_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 12 as u32);
                v_beta_4716_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 13 as u32);
                v_proj_4717_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 14 as u32);
                v_zeta_4718_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 15 as u32);
                v_zetaDelta_4719_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 16 as u32);
                v_zetaUnused_4720_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 17 as u32);
                v_zetaHave_4721_ = crate::leanh::lean_ctor_get_uint8(v___x_4703_, 18 as u32);
                v_isSharedCheck_4757_ = (!crate::leanh::lean_is_exclusive(v___x_4703_)) as u8;
                if v_isSharedCheck_4757_ == 0 {
                    v___x_4723_ = v___x_4703_;
                    v_isShared_4724_ = v_isSharedCheck_4757_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4703_);
                    v___x_4723_ = crate::leanh::lean_box(0);
                    v_isShared_4724_ = v_isSharedCheck_4757_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_trackZetaDelta_4725_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4726_ = crate::leanh::lean_ctor_get(v___y_4699_, 1);
                v_lctx_4727_ = crate::leanh::lean_ctor_get(v___y_4699_, 2);
                v_localInstances_4728_ = crate::leanh::lean_ctor_get(v___y_4699_, 3);
                v_defEqCtx_x3f_4729_ = crate::leanh::lean_ctor_get(v___y_4699_, 4);
                v_synthPendingDepth_4730_ = crate::leanh::lean_ctor_get(v___y_4699_, 5);
                v_canUnfold_x3f_4731_ = crate::leanh::lean_ctor_get(v___y_4699_, 6);
                v_univApprox_4732_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4733_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4734_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_4735_ = 1;
                if v_isShared_4724_ == 0 {
                    v___x_4737_ = v___x_4723_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4756_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        0 as u32,
                        v_foApprox_4704_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        1 as u32,
                        v_ctxApprox_4705_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        2 as u32,
                        v_quasiPatternApprox_4706_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        3 as u32,
                        v_constApprox_4707_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        4 as u32,
                        v_isDefEqStuckEx_4708_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        5 as u32,
                        v_unificationHints_4709_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        6 as u32,
                        v_proofIrrelevance_4710_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        8 as u32,
                        v_offsetCnstrs_4711_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        9 as u32,
                        v_transparency_4712_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        10 as u32,
                        v_etaStruct_4713_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        11 as u32,
                        v_univApprox_4714_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        12 as u32,
                        v_iota_4715_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        13 as u32,
                        v_beta_4716_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        14 as u32,
                        v_proj_4717_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        15 as u32,
                        v_zeta_4718_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        16 as u32,
                        v_zetaDelta_4719_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        17 as u32,
                        v_zetaUnused_4720_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        18 as u32,
                        v_zetaHave_4721_,
                    );
                    v___x_4737_ = v_reuseFailAlloc_4756_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(v___x_4737_, 7 as u32, v___x_4735_);
                v___x_4738_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4737_);
                v___x_4739_ = crate::leanh::lean_box(0);
                v___x_4740_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__5;
                v___x_4741_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_4741_, 0, v___x_4737_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_4741_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4738_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_4731_);
                crate::leanh::lean_inc(v_synthPendingDepth_4730_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_4729_);
                crate::leanh::lean_inc_ref(v_localInstances_4728_);
                crate::leanh::lean_inc_ref(v_lctx_4727_);
                crate::leanh::lean_inc(v_zetaDeltaSet_4726_);
                v___x_4742_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_4742_, 0, v___x_4741_);
                crate::leanh::lean_ctor_set(v___x_4742_, 1, v_zetaDeltaSet_4726_);
                crate::leanh::lean_ctor_set(v___x_4742_, 2, v_lctx_4727_);
                crate::leanh::lean_ctor_set(v___x_4742_, 3, v_localInstances_4728_);
                crate::leanh::lean_ctor_set(v___x_4742_, 4, v_defEqCtx_x3f_4729_);
                crate::leanh::lean_ctor_set(v___x_4742_, 5, v_synthPendingDepth_4730_);
                crate::leanh::lean_ctor_set(v___x_4742_, 6, v_canUnfold_x3f_4731_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4742_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4725_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4742_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4732_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4742_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4733_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4742_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4734_,
                );
                crate::leanh::lean_inc_ref(v_H_4585_);
                v___x_4743_ = l_Lean_Meta_Sym_isDefEqS(
                    v_H_4585_,
                    v_T_4586_,
                    v___x_4735_,
                    v___x_4735_,
                    v___x_4740_,
                    v___x_4740_,
                    v___y_4697_,
                    v___y_4698_,
                    v___x_4742_,
                    v___y_4700_,
                    v___y_4701_,
                    v___y_4702_,
                );
                crate::leanh::lean_dec_ref_known(v___x_4742_, 7);
                if crate::leanh::lean_obj_tag(v___x_4743_) == 0 {
                    v_a_4744_ = crate::leanh::lean_ctor_get(v___x_4743_, 0);
                    crate::leanh::lean_inc(v_a_4744_);
                    crate::leanh::lean_dec_ref_known(v___x_4743_, 1);
                    v___x_4745_ = (crate::leanh::lean_unbox(v_a_4744_) as u8);
                    crate::leanh::lean_dec(v_a_4744_);
                    v___y_4631_ = v___y_4701_;
                    v___y_4632_ = v___y_4692_;
                    v___y_4633_ = v___y_4700_;
                    v___y_4634_ = v___y_4702_;
                    v___y_4635_ = v___y_4695_;
                    v___y_4636_ = v___y_4699_;
                    v___y_4637_ = v___y_4693_;
                    v___y_4638_ = v___y_4698_;
                    v___y_4639_ = v___x_4739_;
                    v___y_4640_ = v___y_4696_;
                    v___y_4641_ = v___y_4694_;
                    v___y_4642_ = v___y_4697_;
                    v_a_4643_ = v___x_4745_;
                    state = 4;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_4743_) == 0 {
                        v_a_4746_ = crate::leanh::lean_ctor_get(v___x_4743_, 0);
                        crate::leanh::lean_inc(v_a_4746_);
                        crate::leanh::lean_dec_ref_known(v___x_4743_, 1);
                        v___x_4747_ = (crate::leanh::lean_unbox(v_a_4746_) as u8);
                        crate::leanh::lean_dec(v_a_4746_);
                        v___y_4631_ = v___y_4701_;
                        v___y_4632_ = v___y_4692_;
                        v___y_4633_ = v___y_4700_;
                        v___y_4634_ = v___y_4702_;
                        v___y_4635_ = v___y_4695_;
                        v___y_4636_ = v___y_4699_;
                        v___y_4637_ = v___y_4693_;
                        v___y_4638_ = v___y_4698_;
                        v___y_4639_ = v___x_4739_;
                        v___y_4640_ = v___y_4696_;
                        v___y_4641_ = v___y_4694_;
                        v___y_4642_ = v___y_4697_;
                        v_a_4643_ = v___x_4747_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_H_4585_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4584_);
                        crate::leanh::lean_dec(v_goal_4582_);
                        v_a_4748_ = crate::leanh::lean_ctor_get(v___x_4743_, 0);
                        v_isSharedCheck_4755_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4743_)) as u8;
                        if v_isSharedCheck_4755_ == 0 {
                            v___x_4750_ = v___x_4743_;
                            v_isShared_4751_ = v_isSharedCheck_4755_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4748_);
                            crate::leanh::lean_dec(v___x_4743_);
                            v___x_4750_ = crate::leanh::lean_box(0);
                            v_isShared_4751_ = v_isSharedCheck_4755_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            17 => {
                if v_isShared_4751_ == 0 {
                    v___x_4753_ = v___x_4750_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4754_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
                    v___x_4753_ = v_reuseFailAlloc_4754_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4753_;
            }
            19 => {
                if v_isShared_4767_ == 0 {
                    v___x_4769_ = v___x_4766_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4770_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
                    v___x_4769_ = v_reuseFailAlloc_4770_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4769_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_goal_4772_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_ent_4773_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3s_4774_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_H_4775_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_T_4776_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_4777_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_4778_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_4779_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_4780_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_4781_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_4782_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_4783_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_4784_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_4785_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_4786_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_4787_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_4788_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4789_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails(v_goal_4772_, v_ent_4773_, v_00_u03c3s_4774_, v_H_4775_, v_T_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_);
    crate::leanh::lean_dec(v_a_4787_);
    crate::leanh::lean_dec_ref(v_a_4786_);
    crate::leanh::lean_dec(v_a_4785_);
    crate::leanh::lean_dec_ref(v_a_4784_);
    crate::leanh::lean_dec(v_a_4783_);
    crate::leanh::lean_dec_ref(v_a_4782_);
    crate::leanh::lean_dec(v_a_4781_);
    crate::leanh::lean_dec_ref(v_a_4780_);
    crate::leanh::lean_dec(v_a_4779_);
    crate::leanh::lean_dec(v_a_4778_);
    crate::leanh::lean_dec_ref(v_a_4777_);
    crate::leanh::lean_dec_ref(v_ent_4773_);
    return v_res_4789_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0(
    mut v_mvarId_4790_: *mut crate::leanh::LeanObject,
    mut v_val_4791_: *mut crate::leanh::LeanObject,
    mut v___y_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
    mut v___y_4801_: *mut crate::leanh::LeanObject,
    mut v___y_4802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4804_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___redArg(v_mvarId_4790_, v_val_4791_, v___y_4800_);
    return v___x_4804_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___boxed(
    mut v_mvarId_4805_: *mut crate::leanh::LeanObject,
    mut v_val_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
    mut v___y_4809_: *mut crate::leanh::LeanObject,
    mut v___y_4810_: *mut crate::leanh::LeanObject,
    mut v___y_4811_: *mut crate::leanh::LeanObject,
    mut v___y_4812_: *mut crate::leanh::LeanObject,
    mut v___y_4813_: *mut crate::leanh::LeanObject,
    mut v___y_4814_: *mut crate::leanh::LeanObject,
    mut v___y_4815_: *mut crate::leanh::LeanObject,
    mut v___y_4816_: *mut crate::leanh::LeanObject,
    mut v___y_4817_: *mut crate::leanh::LeanObject,
    mut v___y_4818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4819_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0(v_mvarId_4805_, v_val_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_);
    crate::leanh::lean_dec(v___y_4817_);
    crate::leanh::lean_dec_ref(v___y_4816_);
    crate::leanh::lean_dec(v___y_4815_);
    crate::leanh::lean_dec_ref(v___y_4814_);
    crate::leanh::lean_dec(v___y_4813_);
    crate::leanh::lean_dec_ref(v___y_4812_);
    crate::leanh::lean_dec(v___y_4811_);
    crate::leanh::lean_dec_ref(v___y_4810_);
    crate::leanh::lean_dec(v___y_4809_);
    crate::leanh::lean_dec(v___y_4808_);
    crate::leanh::lean_dec_ref(v___y_4807_);
    return v_res_4819_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0(
    mut v_00_u03b2_4820_: *mut crate::leanh::LeanObject,
    mut v_x_4821_: *mut crate::leanh::LeanObject,
    mut v_x_4822_: *mut crate::leanh::LeanObject,
    mut v_x_4823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4824_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0___redArg(v_x_4821_, v_x_4822_, v_x_4823_);
    return v___x_4824_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4825_: *mut crate::leanh::LeanObject,
    mut v_x_4826_: *mut crate::leanh::LeanObject,
    mut v_x_4827_: usize,
    mut v_x_4828_: usize,
    mut v_x_4829_: *mut crate::leanh::LeanObject,
    mut v_x_4830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg(v_x_4826_, v_x_4827_, v_x_4828_, v_x_4829_, v_x_4830_);
    return v___x_4831_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4832_: *mut crate::leanh::LeanObject,
    mut v_x_4833_: *mut crate::leanh::LeanObject,
    mut v_x_4834_: *mut crate::leanh::LeanObject,
    mut v_x_4835_: *mut crate::leanh::LeanObject,
    mut v_x_4836_: *mut crate::leanh::LeanObject,
    mut v_x_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_29457__boxed_4838_: usize = 0;
    let mut v_x_29458__boxed_4839_: usize = 0;
    let mut v_res_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_29457__boxed_4838_ = crate::leanh::lean_unbox_usize(v_x_4834_);
    crate::leanh::lean_dec(v_x_4834_);
    v_x_29458__boxed_4839_ = crate::leanh::lean_unbox_usize(v_x_4835_);
    crate::leanh::lean_dec(v_x_4835_);
    v_res_4840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1(v_00_u03b2_4832_, v_x_4833_, v_x_29457__boxed_4838_, v_x_29458__boxed_4839_, v_x_4836_, v_x_4837_);
    return v_res_4840_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4841_: *mut crate::leanh::LeanObject,
    mut v_n_4842_: *mut crate::leanh::LeanObject,
    mut v_k_4843_: *mut crate::leanh::LeanObject,
    mut v_v_4844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4845_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2___redArg(v_n_4842_, v_k_4843_, v_v_4844_);
    return v___x_4845_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4846_: *mut crate::leanh::LeanObject,
    mut v_depth_4847_: usize,
    mut v_keys_4848_: *mut crate::leanh::LeanObject,
    mut v_vals_4849_: *mut crate::leanh::LeanObject,
    mut v_heq_4850_: *mut crate::leanh::LeanObject,
    mut v_i_4851_: *mut crate::leanh::LeanObject,
    mut v_entries_4852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4853_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_4847_, v_keys_4848_, v_vals_4849_, v_i_4851_, v_entries_4852_);
    return v___x_4853_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4854_: *mut crate::leanh::LeanObject,
    mut v_depth_4855_: *mut crate::leanh::LeanObject,
    mut v_keys_4856_: *mut crate::leanh::LeanObject,
    mut v_vals_4857_: *mut crate::leanh::LeanObject,
    mut v_heq_4858_: *mut crate::leanh::LeanObject,
    mut v_i_4859_: *mut crate::leanh::LeanObject,
    mut v_entries_4860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4861_: usize = 0;
    let mut v_res_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4861_ = crate::leanh::lean_unbox_usize(v_depth_4855_);
    crate::leanh::lean_dec(v_depth_4855_);
    v_res_4862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4854_, v_depth_boxed_4861_, v_keys_4856_, v_vals_4857_, v_heq_4858_, v_i_4859_, v_entries_4860_);
    crate::leanh::lean_dec_ref(v_vals_4857_);
    crate::leanh::lean_dec_ref(v_keys_4856_);
    return v_res_4862_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_4863_: *mut crate::leanh::LeanObject,
    mut v_x_4864_: *mut crate::leanh::LeanObject,
    mut v_x_4865_: *mut crate::leanh::LeanObject,
    mut v_x_4866_: *mut crate::leanh::LeanObject,
    mut v_x_4867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4868_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4864_, v_x_4865_, v_x_4866_, v_x_4867_);
    return v___x_4868_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(
    mut v_args_4869_: *mut crate::leanh::LeanObject,
    mut v_endIdx_4870_: *mut crate::leanh::LeanObject,
    mut v_b_4871_: *mut crate::leanh::LeanObject,
    mut v_i_4872_: *mut crate::leanh::LeanObject,
    mut v___y_4873_: *mut crate::leanh::LeanObject,
    mut v___y_4874_: *mut crate::leanh::LeanObject,
    mut v___y_4875_: *mut crate::leanh::LeanObject,
    mut v___y_4876_: *mut crate::leanh::LeanObject,
    mut v___y_4877_: *mut crate::leanh::LeanObject,
    mut v___y_4878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4880_: u8 = 0;
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4880_ = lean_nat_dec_le(v_endIdx_4870_, v_i_4872_);
                if v___x_4880_ == 0 {
                    v___x_4881_ = l_Lean_instInhabitedExpr;
                    v___x_4882_ = lean_array_get_borrowed(v___x_4881_, v_args_4869_, v_i_4872_);
                    crate::leanh::lean_inc(v___x_4882_);
                    v___x_4883_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_b_4871_, v___x_4882_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
                    if crate::leanh::lean_obj_tag(v___x_4883_) == 0 {
                        v_a_4884_ = crate::leanh::lean_ctor_get(v___x_4883_, 0);
                        crate::leanh::lean_inc(v_a_4884_);
                        crate::leanh::lean_dec_ref_known(v___x_4883_, 1);
                        v___x_4885_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4886_ = lean_nat_add(v_i_4872_, v___x_4885_);
                        crate::leanh::lean_dec(v_i_4872_);
                        v_b_4871_ = v_a_4884_;
                        v_i_4872_ = v___x_4886_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4872_);
                        return v___x_4883_;
                    }
                } else {
                    crate::leanh::lean_dec(v_i_4872_);
                    v___x_4888_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4888_, 0, v_b_4871_);
                    return v___x_4888_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg___boxed(
    mut v_args_4889_: *mut crate::leanh::LeanObject,
    mut v_endIdx_4890_: *mut crate::leanh::LeanObject,
    mut v_b_4891_: *mut crate::leanh::LeanObject,
    mut v_i_4892_: *mut crate::leanh::LeanObject,
    mut v___y_4893_: *mut crate::leanh::LeanObject,
    mut v___y_4894_: *mut crate::leanh::LeanObject,
    mut v___y_4895_: *mut crate::leanh::LeanObject,
    mut v___y_4896_: *mut crate::leanh::LeanObject,
    mut v___y_4897_: *mut crate::leanh::LeanObject,
    mut v___y_4898_: *mut crate::leanh::LeanObject,
    mut v___y_4899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4900_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_4889_, v_endIdx_4890_, v_b_4891_, v_i_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
    crate::leanh::lean_dec(v___y_4898_);
    crate::leanh::lean_dec_ref(v___y_4897_);
    crate::leanh::lean_dec(v___y_4896_);
    crate::leanh::lean_dec_ref(v___y_4895_);
    crate::leanh::lean_dec(v___y_4894_);
    crate::leanh::lean_dec_ref(v___y_4893_);
    crate::leanh::lean_dec(v_endIdx_4890_);
    crate::leanh::lean_dec_ref(v_args_4889_);
    return v_res_4900_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(
    mut v_f_4901_: *mut crate::leanh::LeanObject,
    mut v_args_4902_: *mut crate::leanh::LeanObject,
    mut v___y_4903_: *mut crate::leanh::LeanObject,
    mut v___y_4904_: *mut crate::leanh::LeanObject,
    mut v___y_4905_: *mut crate::leanh::LeanObject,
    mut v___y_4906_: *mut crate::leanh::LeanObject,
    mut v___y_4907_: *mut crate::leanh::LeanObject,
    mut v___y_4908_: *mut crate::leanh::LeanObject,
    mut v___y_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
    mut v___y_4911_: *mut crate::leanh::LeanObject,
    mut v___y_4912_: *mut crate::leanh::LeanObject,
    mut v___y_4913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4915_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4916_ = lean_array_get_size(v_args_4902_);
    v___x_4917_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_4902_, v___x_4916_, v_f_4901_, v___x_4915_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_);
    return v___x_4917_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1___boxed(
    mut v_f_4918_: *mut crate::leanh::LeanObject,
    mut v_args_4919_: *mut crate::leanh::LeanObject,
    mut v___y_4920_: *mut crate::leanh::LeanObject,
    mut v___y_4921_: *mut crate::leanh::LeanObject,
    mut v___y_4922_: *mut crate::leanh::LeanObject,
    mut v___y_4923_: *mut crate::leanh::LeanObject,
    mut v___y_4924_: *mut crate::leanh::LeanObject,
    mut v___y_4925_: *mut crate::leanh::LeanObject,
    mut v___y_4926_: *mut crate::leanh::LeanObject,
    mut v___y_4927_: *mut crate::leanh::LeanObject,
    mut v___y_4928_: *mut crate::leanh::LeanObject,
    mut v___y_4929_: *mut crate::leanh::LeanObject,
    mut v___y_4930_: *mut crate::leanh::LeanObject,
    mut v___y_4931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4932_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_f_4918_, v_args_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
    crate::leanh::lean_dec(v___y_4930_);
    crate::leanh::lean_dec_ref(v___y_4929_);
    crate::leanh::lean_dec(v___y_4928_);
    crate::leanh::lean_dec_ref(v___y_4927_);
    crate::leanh::lean_dec(v___y_4926_);
    crate::leanh::lean_dec_ref(v___y_4925_);
    crate::leanh::lean_dec(v___y_4924_);
    crate::leanh::lean_dec_ref(v___y_4923_);
    crate::leanh::lean_dec(v___y_4922_);
    crate::leanh::lean_dec(v___y_4921_);
    crate::leanh::lean_dec_ref(v___y_4920_);
    crate::leanh::lean_dec_ref(v_args_4919_);
    return v_res_4932_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(
    mut v_f_4933_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_4934_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_4935_: *mut crate::leanh::LeanObject,
    mut v_a_u2083_4936_: *mut crate::leanh::LeanObject,
    mut v_a_u2084_4937_: *mut crate::leanh::LeanObject,
    mut v___y_4938_: *mut crate::leanh::LeanObject,
    mut v___y_4939_: *mut crate::leanh::LeanObject,
    mut v___y_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
    mut v___y_4942_: *mut crate::leanh::LeanObject,
    mut v___y_4943_: *mut crate::leanh::LeanObject,
    mut v___y_4944_: *mut crate::leanh::LeanObject,
    mut v___y_4945_: *mut crate::leanh::LeanObject,
    mut v___y_4946_: *mut crate::leanh::LeanObject,
    mut v___y_4947_: *mut crate::leanh::LeanObject,
    mut v___y_4948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4950_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_f_4933_, v_a_u2081_4934_, v_a_u2082_4935_, v_a_u2083_4936_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
    if crate::leanh::lean_obj_tag(v___x_4950_) == 0 {
        let mut v_a_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4951_ = crate::leanh::lean_ctor_get(v___x_4950_, 0);
        crate::leanh::lean_inc(v_a_4951_);
        crate::leanh::lean_dec_ref_known(v___x_4950_, 1);
        v___x_4952_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_4951_, v_a_u2084_4937_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
        return v___x_4952_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2084_4937_);
        return v___x_4950_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_4953_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_u2081_4954_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_a_u2082_4955_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_u2083_4956_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_u2084_4957_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_4958_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4959_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4960_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4961_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4962_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4963_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4964_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4965_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4966_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4967_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4968_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4969_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4970_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_f_4953_, v_a_u2081_4954_, v_a_u2082_4955_, v_a_u2083_4956_, v_a_u2084_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
    crate::leanh::lean_dec(v___y_4968_);
    crate::leanh::lean_dec_ref(v___y_4967_);
    crate::leanh::lean_dec(v___y_4966_);
    crate::leanh::lean_dec_ref(v___y_4965_);
    crate::leanh::lean_dec(v___y_4964_);
    crate::leanh::lean_dec_ref(v___y_4963_);
    crate::leanh::lean_dec(v___y_4962_);
    crate::leanh::lean_dec_ref(v___y_4961_);
    crate::leanh::lean_dec(v___y_4960_);
    crate::leanh::lean_dec(v___y_4959_);
    crate::leanh::lean_dec_ref(v___y_4958_);
    return v_res_4970_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(
    mut v_f_4971_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_4972_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_4973_: *mut crate::leanh::LeanObject,
    mut v_a_u2083_4974_: *mut crate::leanh::LeanObject,
    mut v_a_u2084_4975_: *mut crate::leanh::LeanObject,
    mut v_a_u2085_4976_: *mut crate::leanh::LeanObject,
    mut v___y_4977_: *mut crate::leanh::LeanObject,
    mut v___y_4978_: *mut crate::leanh::LeanObject,
    mut v___y_4979_: *mut crate::leanh::LeanObject,
    mut v___y_4980_: *mut crate::leanh::LeanObject,
    mut v___y_4981_: *mut crate::leanh::LeanObject,
    mut v___y_4982_: *mut crate::leanh::LeanObject,
    mut v___y_4983_: *mut crate::leanh::LeanObject,
    mut v___y_4984_: *mut crate::leanh::LeanObject,
    mut v___y_4985_: *mut crate::leanh::LeanObject,
    mut v___y_4986_: *mut crate::leanh::LeanObject,
    mut v___y_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4989_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_f_4971_, v_a_u2081_4972_, v_a_u2082_4973_, v_a_u2083_4974_, v_a_u2084_4975_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
    if crate::leanh::lean_obj_tag(v___x_4989_) == 0 {
        let mut v_a_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4990_ = crate::leanh::lean_ctor_get(v___x_4989_, 0);
        crate::leanh::lean_inc(v_a_4990_);
        crate::leanh::lean_dec_ref_known(v___x_4989_, 1);
        v___x_4991_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_4990_, v_a_u2085_4976_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
        return v___x_4991_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2085_4976_);
        return v___x_4989_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_4992_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_u2081_4993_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_a_u2082_4994_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_u2083_4995_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_u2084_4996_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_u2085_4997_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4998_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4999_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5000_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5001_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5002_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5003_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5004_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5005_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5006_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5007_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5008_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5009_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5010_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_f_4992_, v_a_u2081_4993_, v_a_u2082_4994_, v_a_u2083_4995_, v_a_u2084_4996_, v_a_u2085_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
    crate::leanh::lean_dec(v___y_5008_);
    crate::leanh::lean_dec_ref(v___y_5007_);
    crate::leanh::lean_dec(v___y_5006_);
    crate::leanh::lean_dec_ref(v___y_5005_);
    crate::leanh::lean_dec(v___y_5004_);
    crate::leanh::lean_dec_ref(v___y_5003_);
    crate::leanh::lean_dec(v___y_5002_);
    crate::leanh::lean_dec_ref(v___y_5001_);
    crate::leanh::lean_dec(v___y_5000_);
    crate::leanh::lean_dec(v___y_4999_);
    crate::leanh::lean_dec_ref(v___y_4998_);
    return v_res_5010_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(
    mut v_goal_5011_: *mut crate::leanh::LeanObject,
    mut v_head_5012_: *mut crate::leanh::LeanObject,
    mut v_H_5013_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5014_: *mut crate::leanh::LeanObject,
    mut v_ent_5015_: *mut crate::leanh::LeanObject,
    mut v_args_5016_: *mut crate::leanh::LeanObject,
    mut v_wpConst_5017_: *mut crate::leanh::LeanObject,
    mut v_m_5018_: *mut crate::leanh::LeanObject,
    mut v_ps_5019_: *mut crate::leanh::LeanObject,
    mut v_instWP_5020_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5021_: *mut crate::leanh::LeanObject,
    mut v_e_x27_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
    mut v_a_5024_: *mut crate::leanh::LeanObject,
    mut v_a_5025_: *mut crate::leanh::LeanObject,
    mut v_a_5026_: *mut crate::leanh::LeanObject,
    mut v_a_5027_: *mut crate::leanh::LeanObject,
    mut v_a_5028_: *mut crate::leanh::LeanObject,
    mut v_a_5029_: *mut crate::leanh::LeanObject,
    mut v_a_5030_: *mut crate::leanh::LeanObject,
    mut v_a_5031_: *mut crate::leanh::LeanObject,
    mut v_a_5032_: *mut crate::leanh::LeanObject,
    mut v_a_5033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5047_: u8 = 0;
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5051_: u8 = 0;
    let mut v_a_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5055_: u8 = 0;
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut v_a_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5035_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_wpConst_5017_, v_m_5018_, v_ps_5019_, v_instWP_5020_, v_00_u03b1_5021_, v_e_x27_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
                if crate::leanh::lean_obj_tag(v___x_5035_) == 0 {
                    v_a_5036_ = crate::leanh::lean_ctor_get(v___x_5035_, 0);
                    crate::leanh::lean_inc(v_a_5036_);
                    crate::leanh::lean_dec_ref_known(v___x_5035_, 1);
                    v___x_5037_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_5038_ = lean_array_set(v_args_5016_, v___x_5037_, v_a_5036_);
                    v___x_5039_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_head_5012_, v___x_5038_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
                    crate::leanh::lean_dec_ref(v___x_5038_);
                    if crate::leanh::lean_obj_tag(v___x_5039_) == 0 {
                        v_a_5040_ = crate::leanh::lean_ctor_get(v___x_5039_, 0);
                        crate::leanh::lean_inc(v_a_5040_);
                        crate::leanh::lean_dec_ref_known(v___x_5039_, 1);
                        v___x_5041_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_5015_, v_00_u03c3s_5014_, v_H_5013_, v_a_5040_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
                        if crate::leanh::lean_obj_tag(v___x_5041_) == 0 {
                            v_a_5042_ = crate::leanh::lean_ctor_get(v___x_5041_, 0);
                            crate::leanh::lean_inc(v_a_5042_);
                            crate::leanh::lean_dec_ref_known(v___x_5041_, 1);
                            v___x_5043_ = l_Lean_MVarId_replaceTargetDefEq(
                                v_goal_5011_,
                                v_a_5042_,
                                v_a_5030_,
                                v_a_5031_,
                                v_a_5032_,
                                v_a_5033_,
                            );
                            return v___x_5043_;
                        } else {
                            crate::leanh::lean_dec(v_goal_5011_);
                            v_a_5044_ = crate::leanh::lean_ctor_get(v___x_5041_, 0);
                            v_isSharedCheck_5051_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5041_)) as u8;
                            if v_isSharedCheck_5051_ == 0 {
                                v___x_5046_ = v___x_5041_;
                                v_isShared_5047_ = v_isSharedCheck_5051_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5044_);
                                crate::leanh::lean_dec(v___x_5041_);
                                v___x_5046_ = crate::leanh::lean_box(0);
                                v_isShared_5047_ = v_isSharedCheck_5051_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ent_5015_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_5014_);
                        crate::leanh::lean_dec_ref(v_H_5013_);
                        crate::leanh::lean_dec(v_goal_5011_);
                        v_a_5052_ = crate::leanh::lean_ctor_get(v___x_5039_, 0);
                        v_isSharedCheck_5059_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5039_)) as u8;
                        if v_isSharedCheck_5059_ == 0 {
                            v___x_5054_ = v___x_5039_;
                            v_isShared_5055_ = v_isSharedCheck_5059_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5052_);
                            crate::leanh::lean_dec(v___x_5039_);
                            v___x_5054_ = crate::leanh::lean_box(0);
                            v_isShared_5055_ = v_isSharedCheck_5059_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_5016_);
                    crate::leanh::lean_dec_ref(v_ent_5015_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5014_);
                    crate::leanh::lean_dec_ref(v_H_5013_);
                    crate::leanh::lean_dec_ref(v_head_5012_);
                    crate::leanh::lean_dec(v_goal_5011_);
                    v_a_5060_ = crate::leanh::lean_ctor_get(v___x_5035_, 0);
                    v_isSharedCheck_5067_ = (!crate::leanh::lean_is_exclusive(v___x_5035_)) as u8;
                    if v_isSharedCheck_5067_ == 0 {
                        v___x_5062_ = v___x_5035_;
                        v_isShared_5063_ = v_isSharedCheck_5067_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5060_);
                        crate::leanh::lean_dec(v___x_5035_);
                        v___x_5062_ = crate::leanh::lean_box(0);
                        v_isShared_5063_ = v_isSharedCheck_5067_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5047_ == 0 {
                    v___x_5049_ = v___x_5046_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
                    v___x_5049_ = v_reuseFailAlloc_5050_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5049_;
            }
            3 => {
                if v_isShared_5055_ == 0 {
                    v___x_5057_ = v___x_5054_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
                    v___x_5057_ = v_reuseFailAlloc_5058_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5057_;
            }
            5 => {
                if v_isShared_5063_ == 0 {
                    v___x_5065_ = v___x_5062_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
                    v___x_5065_ = v_reuseFailAlloc_5066_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_goal_5068_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_head_5069_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_H_5070_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_5071_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ent_5072_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_args_5073_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_wpConst_5074_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_m_5075_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_ps_5076_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_instWP_5077_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_00_u03b1_5078_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_e_x27_5079_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_5080_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_5081_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_5082_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_5083_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_5084_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_5085_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_5086_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_a_5087_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_a_5088_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_a_5089_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_a_5090_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_a_5091_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v_res_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5092_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_5068_, v_head_5069_, v_H_5070_, v_00_u03c3s_5071_, v_ent_5072_, v_args_5073_, v_wpConst_5074_, v_m_5075_, v_ps_5076_, v_instWP_5077_, v_00_u03b1_5078_, v_e_x27_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_);
    crate::leanh::lean_dec(v_a_5090_);
    crate::leanh::lean_dec_ref(v_a_5089_);
    crate::leanh::lean_dec(v_a_5088_);
    crate::leanh::lean_dec_ref(v_a_5087_);
    crate::leanh::lean_dec(v_a_5086_);
    crate::leanh::lean_dec_ref(v_a_5085_);
    crate::leanh::lean_dec(v_a_5084_);
    crate::leanh::lean_dec_ref(v_a_5083_);
    crate::leanh::lean_dec(v_a_5082_);
    crate::leanh::lean_dec(v_a_5081_);
    crate::leanh::lean_dec_ref(v_a_5080_);
    return v_res_5092_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2(
    mut v_args_5093_: *mut crate::leanh::LeanObject,
    mut v_endIdx_5094_: *mut crate::leanh::LeanObject,
    mut v_b_5095_: *mut crate::leanh::LeanObject,
    mut v_i_5096_: *mut crate::leanh::LeanObject,
    mut v___y_5097_: *mut crate::leanh::LeanObject,
    mut v___y_5098_: *mut crate::leanh::LeanObject,
    mut v___y_5099_: *mut crate::leanh::LeanObject,
    mut v___y_5100_: *mut crate::leanh::LeanObject,
    mut v___y_5101_: *mut crate::leanh::LeanObject,
    mut v___y_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
    mut v___y_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5109_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_5093_, v_endIdx_5094_, v_b_5095_, v_i_5096_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
    return v___x_5109_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___boxed(
    mut v_args_5110_: *mut crate::leanh::LeanObject,
    mut v_endIdx_5111_: *mut crate::leanh::LeanObject,
    mut v_b_5112_: *mut crate::leanh::LeanObject,
    mut v_i_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
    mut v___y_5117_: *mut crate::leanh::LeanObject,
    mut v___y_5118_: *mut crate::leanh::LeanObject,
    mut v___y_5119_: *mut crate::leanh::LeanObject,
    mut v___y_5120_: *mut crate::leanh::LeanObject,
    mut v___y_5121_: *mut crate::leanh::LeanObject,
    mut v___y_5122_: *mut crate::leanh::LeanObject,
    mut v___y_5123_: *mut crate::leanh::LeanObject,
    mut v___y_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5126_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2(v_args_5110_, v_endIdx_5111_, v_b_5112_, v_i_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
    crate::leanh::lean_dec(v___y_5124_);
    crate::leanh::lean_dec_ref(v___y_5123_);
    crate::leanh::lean_dec(v___y_5122_);
    crate::leanh::lean_dec_ref(v___y_5121_);
    crate::leanh::lean_dec(v___y_5120_);
    crate::leanh::lean_dec_ref(v___y_5119_);
    crate::leanh::lean_dec(v___y_5118_);
    crate::leanh::lean_dec_ref(v___y_5117_);
    crate::leanh::lean_dec(v___y_5116_);
    crate::leanh::lean_dec(v___y_5115_);
    crate::leanh::lean_dec_ref(v___y_5114_);
    crate::leanh::lean_dec(v_endIdx_5111_);
    crate::leanh::lean_dec_ref(v_args_5110_);
    return v_res_5126_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(
    mut v_revArgs_5127_: *mut crate::leanh::LeanObject,
    mut v_start_5128_: *mut crate::leanh::LeanObject,
    mut v_b_5129_: *mut crate::leanh::LeanObject,
    mut v_i_5130_: *mut crate::leanh::LeanObject,
    mut v___y_5131_: *mut crate::leanh::LeanObject,
    mut v___y_5132_: *mut crate::leanh::LeanObject,
    mut v___y_5133_: *mut crate::leanh::LeanObject,
    mut v___y_5134_: *mut crate::leanh::LeanObject,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5138_: u8 = 0;
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5138_ = lean_nat_dec_le(v_i_5130_, v_start_5128_);
                if v___x_5138_ == 0 {
                    v___x_5139_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_i_5140_ = lean_nat_sub(v_i_5130_, v___x_5139_);
                    crate::leanh::lean_dec(v_i_5130_);
                    v___x_5141_ = l_Lean_instInhabitedExpr;
                    v___x_5142_ = lean_array_get_borrowed(v___x_5141_, v_revArgs_5127_, v_i_5140_);
                    crate::leanh::lean_inc(v___x_5142_);
                    v___x_5143_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_b_5129_, v___x_5142_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
                    if crate::leanh::lean_obj_tag(v___x_5143_) == 0 {
                        v_a_5144_ = crate::leanh::lean_ctor_get(v___x_5143_, 0);
                        crate::leanh::lean_inc(v_a_5144_);
                        crate::leanh::lean_dec_ref_known(v___x_5143_, 1);
                        v_b_5129_ = v_a_5144_;
                        v_i_5130_ = v_i_5140_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_5140_);
                        return v___x_5143_;
                    }
                } else {
                    crate::leanh::lean_dec(v_i_5130_);
                    v___x_5146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5146_, 0, v_b_5129_);
                    return v___x_5146_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg___boxed(
    mut v_revArgs_5147_: *mut crate::leanh::LeanObject,
    mut v_start_5148_: *mut crate::leanh::LeanObject,
    mut v_b_5149_: *mut crate::leanh::LeanObject,
    mut v_i_5150_: *mut crate::leanh::LeanObject,
    mut v___y_5151_: *mut crate::leanh::LeanObject,
    mut v___y_5152_: *mut crate::leanh::LeanObject,
    mut v___y_5153_: *mut crate::leanh::LeanObject,
    mut v___y_5154_: *mut crate::leanh::LeanObject,
    mut v___y_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5158_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_5147_, v_start_5148_, v_b_5149_, v_i_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_);
    crate::leanh::lean_dec(v___y_5156_);
    crate::leanh::lean_dec_ref(v___y_5155_);
    crate::leanh::lean_dec(v___y_5154_);
    crate::leanh::lean_dec_ref(v___y_5153_);
    crate::leanh::lean_dec(v___y_5152_);
    crate::leanh::lean_dec_ref(v___y_5151_);
    crate::leanh::lean_dec(v_start_5148_);
    crate::leanh::lean_dec_ref(v_revArgs_5147_);
    return v_res_5158_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(
    mut v_f_5159_: *mut crate::leanh::LeanObject,
    mut v_revArgs_5160_: *mut crate::leanh::LeanObject,
    mut v___y_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
    mut v___y_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
    mut v___y_5168_: *mut crate::leanh::LeanObject,
    mut v___y_5169_: *mut crate::leanh::LeanObject,
    mut v___y_5170_: *mut crate::leanh::LeanObject,
    mut v___y_5171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5173_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5174_ = lean_array_get_size(v_revArgs_5160_);
    v___x_5175_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_5160_, v___x_5173_, v_f_5159_, v___x_5174_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_);
    return v___x_5175_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0___boxed(
    mut v_f_5176_: *mut crate::leanh::LeanObject,
    mut v_revArgs_5177_: *mut crate::leanh::LeanObject,
    mut v___y_5178_: *mut crate::leanh::LeanObject,
    mut v___y_5179_: *mut crate::leanh::LeanObject,
    mut v___y_5180_: *mut crate::leanh::LeanObject,
    mut v___y_5181_: *mut crate::leanh::LeanObject,
    mut v___y_5182_: *mut crate::leanh::LeanObject,
    mut v___y_5183_: *mut crate::leanh::LeanObject,
    mut v___y_5184_: *mut crate::leanh::LeanObject,
    mut v___y_5185_: *mut crate::leanh::LeanObject,
    mut v___y_5186_: *mut crate::leanh::LeanObject,
    mut v___y_5187_: *mut crate::leanh::LeanObject,
    mut v___y_5188_: *mut crate::leanh::LeanObject,
    mut v___y_5189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5190_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(v_f_5176_, v_revArgs_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_);
    crate::leanh::lean_dec(v___y_5188_);
    crate::leanh::lean_dec_ref(v___y_5187_);
    crate::leanh::lean_dec(v___y_5186_);
    crate::leanh::lean_dec_ref(v___y_5185_);
    crate::leanh::lean_dec(v___y_5184_);
    crate::leanh::lean_dec_ref(v___y_5183_);
    crate::leanh::lean_dec(v___y_5182_);
    crate::leanh::lean_dec_ref(v___y_5181_);
    crate::leanh::lean_dec(v___y_5180_);
    crate::leanh::lean_dec(v___y_5179_);
    crate::leanh::lean_dec_ref(v___y_5178_);
    crate::leanh::lean_dec_ref(v_revArgs_5177_);
    return v_res_5190_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5192_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0;
    v___x_5193_ = l_Lean_stringToMessageData(v___x_5192_);
    return v___x_5193_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(
    mut v_goal_5194_: *mut crate::leanh::LeanObject,
    mut v_head_5195_: *mut crate::leanh::LeanObject,
    mut v_H_5196_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5197_: *mut crate::leanh::LeanObject,
    mut v_ent_5198_: *mut crate::leanh::LeanObject,
    mut v_args_5199_: *mut crate::leanh::LeanObject,
    mut v_wpConst_5200_: *mut crate::leanh::LeanObject,
    mut v_m_5201_: *mut crate::leanh::LeanObject,
    mut v_ps_5202_: *mut crate::leanh::LeanObject,
    mut v_instWP_5203_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5204_: *mut crate::leanh::LeanObject,
    mut v_e_5205_: *mut crate::leanh::LeanObject,
    mut v_f_5206_: *mut crate::leanh::LeanObject,
    mut v_a_5207_: *mut crate::leanh::LeanObject,
    mut v_a_5208_: *mut crate::leanh::LeanObject,
    mut v_a_5209_: *mut crate::leanh::LeanObject,
    mut v_a_5210_: *mut crate::leanh::LeanObject,
    mut v_a_5211_: *mut crate::leanh::LeanObject,
    mut v_a_5212_: *mut crate::leanh::LeanObject,
    mut v_a_5213_: *mut crate::leanh::LeanObject,
    mut v_a_5214_: *mut crate::leanh::LeanObject,
    mut v_a_5215_: *mut crate::leanh::LeanObject,
    mut v_a_5216_: *mut crate::leanh::LeanObject,
    mut v_a_5217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_5223_: u8 = 0;
    let mut v___y_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5254_: u8 = 0;
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5259_: u8 = 0;
    let mut v_a_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5263_: u8 = 0;
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut v_a_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5271_: u8 = 0;
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut v_a_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut v_a_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5287_: u8 = 0;
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5291_: u8 = 0;
    let mut v_a_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5295_: u8 = 0;
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5299_: u8 = 0;
    let mut v_options_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5301_: u8 = 0;
    let mut v_inheritedTraceOptions_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: u8 = 0;
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5313_: u8 = 0;
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_f_5206_) == 8 {
                    v_declName_5219_ = crate::leanh::lean_ctor_get(v_f_5206_, 0);
                    crate::leanh::lean_inc(v_declName_5219_);
                    v_type_5220_ = crate::leanh::lean_ctor_get(v_f_5206_, 1);
                    crate::leanh::lean_inc_ref(v_type_5220_);
                    v_value_5221_ = crate::leanh::lean_ctor_get(v_f_5206_, 2);
                    crate::leanh::lean_inc_ref(v_value_5221_);
                    v_body_5222_ = crate::leanh::lean_ctor_get(v_f_5206_, 3);
                    crate::leanh::lean_inc_ref(v_body_5222_);
                    v_nondep_5223_ = crate::leanh::lean_ctor_get_uint8(
                        v_f_5206_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_f_5206_, 4);
                    v_options_5300_ = crate::leanh::lean_ctor_get(v_a_5216_, 2);
                    v_hasTrace_5301_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_5300_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5301_ == 0 {
                        v___y_5225_ = v_a_5207_;
                        v___y_5226_ = v_a_5208_;
                        v___y_5227_ = v_a_5209_;
                        v___y_5228_ = v_a_5210_;
                        v___y_5229_ = v_a_5211_;
                        v___y_5230_ = v_a_5212_;
                        v___y_5231_ = v_a_5213_;
                        v___y_5232_ = v_a_5214_;
                        v___y_5233_ = v_a_5215_;
                        v___y_5234_ = v_a_5216_;
                        v___y_5235_ = v_a_5217_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5302_ = crate::leanh::lean_ctor_get(v_a_5216_, 13);
                        v_cls_5303_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                        v___x_5304_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
                        v___x_5305_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5302_,
                            v_options_5300_,
                            v___x_5304_,
                        );
                        if v___x_5305_ == 0 {
                            v___y_5225_ = v_a_5207_;
                            v___y_5226_ = v_a_5208_;
                            v___y_5227_ = v_a_5209_;
                            v___y_5228_ = v_a_5210_;
                            v___y_5229_ = v_a_5211_;
                            v___y_5230_ = v_a_5212_;
                            v___y_5231_ = v_a_5213_;
                            v___y_5232_ = v_a_5214_;
                            v___y_5233_ = v_a_5215_;
                            v___y_5234_ = v_a_5216_;
                            v___y_5235_ = v_a_5217_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5306_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1);
                            crate::leanh::lean_inc(v_declName_5219_);
                            v___x_5307_ = l_Lean_MessageData_ofName(v_declName_5219_);
                            v___x_5308_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5308_, 0, v___x_5306_);
                            crate::leanh::lean_ctor_set(v___x_5308_, 1, v___x_5307_);
                            v___x_5309_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_5303_, v___x_5308_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
                            if crate::leanh::lean_obj_tag(v___x_5309_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5309_, 1);
                                v___y_5225_ = v_a_5207_;
                                v___y_5226_ = v_a_5208_;
                                v___y_5227_ = v_a_5209_;
                                v___y_5228_ = v_a_5210_;
                                v___y_5229_ = v_a_5211_;
                                v___y_5230_ = v_a_5212_;
                                v___y_5231_ = v_a_5213_;
                                v___y_5232_ = v_a_5214_;
                                v___y_5233_ = v_a_5215_;
                                v___y_5234_ = v_a_5216_;
                                v___y_5235_ = v_a_5217_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_body_5222_);
                                crate::leanh::lean_dec_ref(v_value_5221_);
                                crate::leanh::lean_dec_ref(v_type_5220_);
                                crate::leanh::lean_dec(v_declName_5219_);
                                crate::leanh::lean_dec_ref(v_e_5205_);
                                crate::leanh::lean_dec_ref(v_00_u03b1_5204_);
                                crate::leanh::lean_dec_ref(v_instWP_5203_);
                                crate::leanh::lean_dec_ref(v_ps_5202_);
                                crate::leanh::lean_dec_ref(v_m_5201_);
                                crate::leanh::lean_dec_ref(v_wpConst_5200_);
                                crate::leanh::lean_dec_ref(v_args_5199_);
                                crate::leanh::lean_dec_ref(v_ent_5198_);
                                crate::leanh::lean_dec_ref(v_00_u03c3s_5197_);
                                crate::leanh::lean_dec_ref(v_H_5196_);
                                crate::leanh::lean_dec_ref(v_head_5195_);
                                crate::leanh::lean_dec(v_goal_5194_);
                                v_a_5310_ = crate::leanh::lean_ctor_get(v___x_5309_, 0);
                                v_isSharedCheck_5317_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5309_)) as u8;
                                if v_isSharedCheck_5317_ == 0 {
                                    v___x_5312_ = v___x_5309_;
                                    v_isShared_5313_ = v_isSharedCheck_5317_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5310_);
                                    crate::leanh::lean_dec(v___x_5309_);
                                    v___x_5312_ = crate::leanh::lean_box(0);
                                    v_isShared_5313_ = v_isSharedCheck_5317_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5206_);
                    crate::leanh::lean_dec_ref(v_e_5205_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5204_);
                    crate::leanh::lean_dec_ref(v_instWP_5203_);
                    crate::leanh::lean_dec_ref(v_ps_5202_);
                    crate::leanh::lean_dec_ref(v_m_5201_);
                    crate::leanh::lean_dec_ref(v_wpConst_5200_);
                    crate::leanh::lean_dec_ref(v_args_5199_);
                    crate::leanh::lean_dec_ref(v_ent_5198_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5197_);
                    crate::leanh::lean_dec_ref(v_H_5196_);
                    crate::leanh::lean_dec_ref(v_head_5195_);
                    crate::leanh::lean_dec(v_goal_5194_);
                    v___x_5318_ = crate::leanh::lean_box(0);
                    v___x_5319_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5319_, 0, v___x_5318_);
                    return v___x_5319_;
                }
            }
            1 => {
                v___x_5236_ = l_Lean_Expr_getAppNumArgs(v_e_5205_);
                v___x_5237_ = lean_mk_empty_array_with_capacity(v___x_5236_);
                crate::leanh::lean_dec(v___x_5236_);
                v___x_5238_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_5205_, v___x_5237_);
                v___x_5239_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(v_body_5222_, v___x_5238_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
                crate::leanh::lean_dec_ref(v___x_5238_);
                if crate::leanh::lean_obj_tag(v___x_5239_) == 0 {
                    v_a_5240_ = crate::leanh::lean_ctor_get(v___x_5239_, 0);
                    crate::leanh::lean_inc(v_a_5240_);
                    crate::leanh::lean_dec_ref_known(v___x_5239_, 1);
                    v___x_5241_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_wpConst_5200_, v_m_5201_, v_ps_5202_, v_instWP_5203_, v_00_u03b1_5204_, v_a_5240_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
                    if crate::leanh::lean_obj_tag(v___x_5241_) == 0 {
                        v_a_5242_ = crate::leanh::lean_ctor_get(v___x_5241_, 0);
                        crate::leanh::lean_inc(v_a_5242_);
                        crate::leanh::lean_dec_ref_known(v___x_5241_, 1);
                        v___x_5243_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_5244_ = lean_array_set(v_args_5199_, v___x_5243_, v_a_5242_);
                        v___x_5245_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_head_5195_, v___x_5244_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
                        crate::leanh::lean_dec_ref(v___x_5244_);
                        if crate::leanh::lean_obj_tag(v___x_5245_) == 0 {
                            v_a_5246_ = crate::leanh::lean_ctor_get(v___x_5245_, 0);
                            crate::leanh::lean_inc(v_a_5246_);
                            crate::leanh::lean_dec_ref_known(v___x_5245_, 1);
                            v___x_5247_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_5198_, v_00_u03c3s_5197_, v_H_5196_, v_a_5246_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
                            if crate::leanh::lean_obj_tag(v___x_5247_) == 0 {
                                v_a_5248_ = crate::leanh::lean_ctor_get(v___x_5247_, 0);
                                crate::leanh::lean_inc(v_a_5248_);
                                crate::leanh::lean_dec_ref_known(v___x_5247_, 1);
                                v___x_5249_ = l_Lean_Expr_letE___override(
                                    v_declName_5219_,
                                    v_type_5220_,
                                    v_value_5221_,
                                    v_a_5248_,
                                    v_nondep_5223_,
                                );
                                v___x_5250_ = l_Lean_MVarId_replaceTargetDefEq(
                                    v_goal_5194_,
                                    v___x_5249_,
                                    v___y_5232_,
                                    v___y_5233_,
                                    v___y_5234_,
                                    v___y_5235_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5250_) == 0 {
                                    v_a_5251_ = crate::leanh::lean_ctor_get(v___x_5250_, 0);
                                    v_isSharedCheck_5259_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5250_)) as u8;
                                    if v_isSharedCheck_5259_ == 0 {
                                        v___x_5253_ = v___x_5250_;
                                        v_isShared_5254_ = v_isSharedCheck_5259_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5251_);
                                        crate::leanh::lean_dec(v___x_5250_);
                                        v___x_5253_ = crate::leanh::lean_box(0);
                                        v_isShared_5254_ = v_isSharedCheck_5259_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_a_5260_ = crate::leanh::lean_ctor_get(v___x_5250_, 0);
                                    v_isSharedCheck_5267_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5250_)) as u8;
                                    if v_isSharedCheck_5267_ == 0 {
                                        v___x_5262_ = v___x_5250_;
                                        v_isShared_5263_ = v_isSharedCheck_5267_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5260_);
                                        crate::leanh::lean_dec(v___x_5250_);
                                        v___x_5262_ = crate::leanh::lean_box(0);
                                        v_isShared_5263_ = v_isSharedCheck_5267_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_value_5221_);
                                crate::leanh::lean_dec_ref(v_type_5220_);
                                crate::leanh::lean_dec(v_declName_5219_);
                                crate::leanh::lean_dec(v_goal_5194_);
                                v_a_5268_ = crate::leanh::lean_ctor_get(v___x_5247_, 0);
                                v_isSharedCheck_5275_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5247_)) as u8;
                                if v_isSharedCheck_5275_ == 0 {
                                    v___x_5270_ = v___x_5247_;
                                    v_isShared_5271_ = v_isSharedCheck_5275_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5268_);
                                    crate::leanh::lean_dec(v___x_5247_);
                                    v___x_5270_ = crate::leanh::lean_box(0);
                                    v_isShared_5271_ = v_isSharedCheck_5275_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_value_5221_);
                            crate::leanh::lean_dec_ref(v_type_5220_);
                            crate::leanh::lean_dec(v_declName_5219_);
                            crate::leanh::lean_dec_ref(v_ent_5198_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_5197_);
                            crate::leanh::lean_dec_ref(v_H_5196_);
                            crate::leanh::lean_dec(v_goal_5194_);
                            v_a_5276_ = crate::leanh::lean_ctor_get(v___x_5245_, 0);
                            v_isSharedCheck_5283_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5245_)) as u8;
                            if v_isSharedCheck_5283_ == 0 {
                                v___x_5278_ = v___x_5245_;
                                v_isShared_5279_ = v_isSharedCheck_5283_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5276_);
                                crate::leanh::lean_dec(v___x_5245_);
                                v___x_5278_ = crate::leanh::lean_box(0);
                                v_isShared_5279_ = v_isSharedCheck_5283_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_value_5221_);
                        crate::leanh::lean_dec_ref(v_type_5220_);
                        crate::leanh::lean_dec(v_declName_5219_);
                        crate::leanh::lean_dec_ref(v_args_5199_);
                        crate::leanh::lean_dec_ref(v_ent_5198_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_5197_);
                        crate::leanh::lean_dec_ref(v_H_5196_);
                        crate::leanh::lean_dec_ref(v_head_5195_);
                        crate::leanh::lean_dec(v_goal_5194_);
                        v_a_5284_ = crate::leanh::lean_ctor_get(v___x_5241_, 0);
                        v_isSharedCheck_5291_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5241_)) as u8;
                        if v_isSharedCheck_5291_ == 0 {
                            v___x_5286_ = v___x_5241_;
                            v_isShared_5287_ = v_isSharedCheck_5291_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5284_);
                            crate::leanh::lean_dec(v___x_5241_);
                            v___x_5286_ = crate::leanh::lean_box(0);
                            v_isShared_5287_ = v_isSharedCheck_5291_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_5221_);
                    crate::leanh::lean_dec_ref(v_type_5220_);
                    crate::leanh::lean_dec(v_declName_5219_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5204_);
                    crate::leanh::lean_dec_ref(v_instWP_5203_);
                    crate::leanh::lean_dec_ref(v_ps_5202_);
                    crate::leanh::lean_dec_ref(v_m_5201_);
                    crate::leanh::lean_dec_ref(v_wpConst_5200_);
                    crate::leanh::lean_dec_ref(v_args_5199_);
                    crate::leanh::lean_dec_ref(v_ent_5198_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5197_);
                    crate::leanh::lean_dec_ref(v_H_5196_);
                    crate::leanh::lean_dec_ref(v_head_5195_);
                    crate::leanh::lean_dec(v_goal_5194_);
                    v_a_5292_ = crate::leanh::lean_ctor_get(v___x_5239_, 0);
                    v_isSharedCheck_5299_ = (!crate::leanh::lean_is_exclusive(v___x_5239_)) as u8;
                    if v_isSharedCheck_5299_ == 0 {
                        v___x_5294_ = v___x_5239_;
                        v_isShared_5295_ = v_isSharedCheck_5299_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5292_);
                        crate::leanh::lean_dec(v___x_5239_);
                        v___x_5294_ = crate::leanh::lean_box(0);
                        v_isShared_5295_ = v_isSharedCheck_5299_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5255_, 0, v_a_5251_);
                if v_isShared_5254_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5253_, 0, v___x_5255_);
                    v___x_5257_ = v___x_5253_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5258_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5258_, 0, v___x_5255_);
                    v___x_5257_ = v_reuseFailAlloc_5258_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5257_;
            }
            4 => {
                if v_isShared_5263_ == 0 {
                    v___x_5265_ = v___x_5262_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5266_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
                    v___x_5265_ = v_reuseFailAlloc_5266_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5265_;
            }
            6 => {
                if v_isShared_5271_ == 0 {
                    v___x_5273_ = v___x_5270_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
                    v___x_5273_ = v_reuseFailAlloc_5274_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5273_;
            }
            8 => {
                if v_isShared_5279_ == 0 {
                    v___x_5281_ = v___x_5278_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
                    v___x_5281_ = v_reuseFailAlloc_5282_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5281_;
            }
            10 => {
                if v_isShared_5287_ == 0 {
                    v___x_5289_ = v___x_5286_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
                    v___x_5289_ = v_reuseFailAlloc_5290_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5289_;
            }
            12 => {
                if v_isShared_5295_ == 0 {
                    v___x_5297_ = v___x_5294_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_a_5292_);
                    v___x_5297_ = v_reuseFailAlloc_5298_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5297_;
            }
            14 => {
                if v_isShared_5313_ == 0 {
                    v___x_5315_ = v___x_5312_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5316_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
                    v___x_5315_ = v_reuseFailAlloc_5316_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_goal_5320_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_head_5321_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_H_5322_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_5323_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ent_5324_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_args_5325_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_wpConst_5326_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_m_5327_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_ps_5328_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_instWP_5329_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_00_u03b1_5330_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_e_5331_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_f_5332_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_5333_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_5334_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_5335_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_5336_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_5337_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_5338_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_a_5339_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_a_5340_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_a_5341_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_a_5342_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_a_5343_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v_a_5344_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v_res_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5345_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(v_goal_5320_, v_head_5321_, v_H_5322_, v_00_u03c3s_5323_, v_ent_5324_, v_args_5325_, v_wpConst_5326_, v_m_5327_, v_ps_5328_, v_instWP_5329_, v_00_u03b1_5330_, v_e_5331_, v_f_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_);
    crate::leanh::lean_dec(v_a_5343_);
    crate::leanh::lean_dec_ref(v_a_5342_);
    crate::leanh::lean_dec(v_a_5341_);
    crate::leanh::lean_dec_ref(v_a_5340_);
    crate::leanh::lean_dec(v_a_5339_);
    crate::leanh::lean_dec_ref(v_a_5338_);
    crate::leanh::lean_dec(v_a_5337_);
    crate::leanh::lean_dec_ref(v_a_5336_);
    crate::leanh::lean_dec(v_a_5335_);
    crate::leanh::lean_dec(v_a_5334_);
    crate::leanh::lean_dec_ref(v_a_5333_);
    return v_res_5345_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0(
    mut v_revArgs_5346_: *mut crate::leanh::LeanObject,
    mut v_start_5347_: *mut crate::leanh::LeanObject,
    mut v_b_5348_: *mut crate::leanh::LeanObject,
    mut v_i_5349_: *mut crate::leanh::LeanObject,
    mut v___y_5350_: *mut crate::leanh::LeanObject,
    mut v___y_5351_: *mut crate::leanh::LeanObject,
    mut v___y_5352_: *mut crate::leanh::LeanObject,
    mut v___y_5353_: *mut crate::leanh::LeanObject,
    mut v___y_5354_: *mut crate::leanh::LeanObject,
    mut v___y_5355_: *mut crate::leanh::LeanObject,
    mut v___y_5356_: *mut crate::leanh::LeanObject,
    mut v___y_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5362_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_5346_, v_start_5347_, v_b_5348_, v_i_5349_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_);
    return v___x_5362_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___boxed(
    mut v_revArgs_5363_: *mut crate::leanh::LeanObject,
    mut v_start_5364_: *mut crate::leanh::LeanObject,
    mut v_b_5365_: *mut crate::leanh::LeanObject,
    mut v_i_5366_: *mut crate::leanh::LeanObject,
    mut v___y_5367_: *mut crate::leanh::LeanObject,
    mut v___y_5368_: *mut crate::leanh::LeanObject,
    mut v___y_5369_: *mut crate::leanh::LeanObject,
    mut v___y_5370_: *mut crate::leanh::LeanObject,
    mut v___y_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
    mut v___y_5375_: *mut crate::leanh::LeanObject,
    mut v___y_5376_: *mut crate::leanh::LeanObject,
    mut v___y_5377_: *mut crate::leanh::LeanObject,
    mut v___y_5378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5379_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0(v_revArgs_5363_, v_start_5364_, v_b_5365_, v_i_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
    crate::leanh::lean_dec(v___y_5377_);
    crate::leanh::lean_dec_ref(v___y_5376_);
    crate::leanh::lean_dec(v___y_5375_);
    crate::leanh::lean_dec_ref(v___y_5374_);
    crate::leanh::lean_dec(v___y_5373_);
    crate::leanh::lean_dec_ref(v___y_5372_);
    crate::leanh::lean_dec(v___y_5371_);
    crate::leanh::lean_dec_ref(v___y_5370_);
    crate::leanh::lean_dec(v___y_5369_);
    crate::leanh::lean_dec(v___y_5368_);
    crate::leanh::lean_dec_ref(v___y_5367_);
    crate::leanh::lean_dec(v_start_5364_);
    crate::leanh::lean_dec_ref(v_revArgs_5363_);
    return v_res_5379_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0()
-> u64 {
    let mut v___x_5380_: u8 = 0;
    let mut v___x_5381_: u64 = 0;
    v___x_5380_ = 2;
    v___x_5381_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_5380_);
    return v___x_5381_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5383_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1;
    v___x_5384_ = l_Lean_stringToMessageData(v___x_5383_);
    return v___x_5384_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5386_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3;
    v___x_5387_ = l_Lean_stringToMessageData(v___x_5386_);
    return v___x_5387_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(
    mut v_goal_5388_: *mut crate::leanh::LeanObject,
    mut v_head_5389_: *mut crate::leanh::LeanObject,
    mut v_H_5390_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5391_: *mut crate::leanh::LeanObject,
    mut v_ent_5392_: *mut crate::leanh::LeanObject,
    mut v_args_5393_: *mut crate::leanh::LeanObject,
    mut v_wpConst_5394_: *mut crate::leanh::LeanObject,
    mut v_m_5395_: *mut crate::leanh::LeanObject,
    mut v_ps_5396_: *mut crate::leanh::LeanObject,
    mut v_instWP_5397_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5398_: *mut crate::leanh::LeanObject,
    mut v_e_5399_: *mut crate::leanh::LeanObject,
    mut v_excessArgs_5400_: *mut crate::leanh::LeanObject,
    mut v_a_5401_: *mut crate::leanh::LeanObject,
    mut v_a_5402_: *mut crate::leanh::LeanObject,
    mut v_a_5403_: *mut crate::leanh::LeanObject,
    mut v_a_5404_: *mut crate::leanh::LeanObject,
    mut v_a_5405_: *mut crate::leanh::LeanObject,
    mut v_a_5406_: *mut crate::leanh::LeanObject,
    mut v_a_5407_: *mut crate::leanh::LeanObject,
    mut v_a_5408_: *mut crate::leanh::LeanObject,
    mut v_a_5409_: *mut crate::leanh::LeanObject,
    mut v_a_5410_: *mut crate::leanh::LeanObject,
    mut v_a_5411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5417_: u8 = 0;
    let mut v_val_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5421_: u8 = 0;
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5423_: u8 = 0;
    let mut v_ctxApprox_5424_: u8 = 0;
    let mut v_quasiPatternApprox_5425_: u8 = 0;
    let mut v_constApprox_5426_: u8 = 0;
    let mut v_isDefEqStuckEx_5427_: u8 = 0;
    let mut v_unificationHints_5428_: u8 = 0;
    let mut v_proofIrrelevance_5429_: u8 = 0;
    let mut v_assignSyntheticOpaque_5430_: u8 = 0;
    let mut v_offsetCnstrs_5431_: u8 = 0;
    let mut v_etaStruct_5432_: u8 = 0;
    let mut v_univApprox_5433_: u8 = 0;
    let mut v_iota_5434_: u8 = 0;
    let mut v_beta_5435_: u8 = 0;
    let mut v_proj_5436_: u8 = 0;
    let mut v_zeta_5437_: u8 = 0;
    let mut v_zetaDelta_5438_: u8 = 0;
    let mut v_zetaUnused_5439_: u8 = 0;
    let mut v_zetaHave_5440_: u8 = 0;
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5443_: u8 = 0;
    let mut v_trackZetaDelta_5444_: u8 = 0;
    let mut v_zetaDeltaSet_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5451_: u8 = 0;
    let mut v_inTypeClassResolution_5452_: u8 = 0;
    let mut v_cacheInferType_5453_: u8 = 0;
    let mut v___x_5454_: u8 = 0;
    let mut v_config_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: u64 = 0;
    let mut v___x_5458_: u64 = 0;
    let mut v___x_5459_: u64 = 0;
    let mut v___x_5460_: u64 = 0;
    let mut v___x_5461_: u64 = 0;
    let mut v_key_5462_: u64 = 0;
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5470_: u8 = 0;
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5477_: u8 = 0;
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5486_: u8 = 0;
    let mut v_a_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5490_: u8 = 0;
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_a_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5498_: u8 = 0;
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5502_: u8 = 0;
    let mut v_isSharedCheck_5503_: u8 = 0;
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5515_: u8 = 0;
    let mut v_mvarIds_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5519_: u8 = 0;
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5526_: u8 = 0;
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5530_: u8 = 0;
    let mut v_a_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5534_: u8 = 0;
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5538_: u8 = 0;
    let mut v_reuseFailAlloc_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5543_: u8 = 0;
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5547_: u8 = 0;
    let mut v_a_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5551_: u8 = 0;
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5555_: u8 = 0;
    let mut v_reuseFailAlloc_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5557_: u8 = 0;
    let mut v_isSharedCheck_5558_: u8 = 0;
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5563_: u8 = 0;
    let mut v_a_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5567_: u8 = 0;
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_5399_);
                v___x_5413_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(
                    v_e_5399_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_,
                );
                if crate::leanh::lean_obj_tag(v___x_5413_) == 0 {
                    v_a_5414_ = crate::leanh::lean_ctor_get(v___x_5413_, 0);
                    v_isSharedCheck_5563_ = (!crate::leanh::lean_is_exclusive(v___x_5413_)) as u8;
                    if v_isSharedCheck_5563_ == 0 {
                        v___x_5416_ = v___x_5413_;
                        v_isShared_5417_ = v_isSharedCheck_5563_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5414_);
                        crate::leanh::lean_dec(v___x_5413_);
                        v___x_5416_ = crate::leanh::lean_box(0);
                        v_isShared_5417_ = v_isSharedCheck_5563_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_excessArgs_5400_);
                    crate::leanh::lean_dec_ref(v_e_5399_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5398_);
                    crate::leanh::lean_dec_ref(v_instWP_5397_);
                    crate::leanh::lean_dec_ref(v_ps_5396_);
                    crate::leanh::lean_dec_ref(v_m_5395_);
                    crate::leanh::lean_dec_ref(v_wpConst_5394_);
                    crate::leanh::lean_dec_ref(v_args_5393_);
                    crate::leanh::lean_dec_ref(v_ent_5392_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5391_);
                    crate::leanh::lean_dec_ref(v_H_5390_);
                    crate::leanh::lean_dec_ref(v_head_5389_);
                    crate::leanh::lean_dec(v_goal_5388_);
                    v_a_5564_ = crate::leanh::lean_ctor_get(v___x_5413_, 0);
                    v_isSharedCheck_5571_ = (!crate::leanh::lean_is_exclusive(v___x_5413_)) as u8;
                    if v_isSharedCheck_5571_ == 0 {
                        v___x_5566_ = v___x_5413_;
                        v_isShared_5567_ = v_isSharedCheck_5571_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5564_);
                        crate::leanh::lean_dec(v___x_5413_);
                        v___x_5566_ = crate::leanh::lean_box(0);
                        v_isShared_5567_ = v_isSharedCheck_5571_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5414_) == 1 {
                    crate::leanh::lean_del_object(v___x_5416_);
                    v_val_5418_ = crate::leanh::lean_ctor_get(v_a_5414_, 0);
                    v_isSharedCheck_5558_ = (!crate::leanh::lean_is_exclusive(v_a_5414_)) as u8;
                    if v_isSharedCheck_5558_ == 0 {
                        v___x_5420_ = v_a_5414_;
                        v_isShared_5421_ = v_isSharedCheck_5558_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5418_);
                        crate::leanh::lean_dec(v_a_5414_);
                        v___x_5420_ = crate::leanh::lean_box(0);
                        v_isShared_5421_ = v_isSharedCheck_5558_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5414_);
                    crate::leanh::lean_dec_ref(v_excessArgs_5400_);
                    crate::leanh::lean_dec_ref(v_e_5399_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5398_);
                    crate::leanh::lean_dec_ref(v_instWP_5397_);
                    crate::leanh::lean_dec_ref(v_ps_5396_);
                    crate::leanh::lean_dec_ref(v_m_5395_);
                    crate::leanh::lean_dec_ref(v_wpConst_5394_);
                    crate::leanh::lean_dec_ref(v_args_5393_);
                    crate::leanh::lean_dec_ref(v_ent_5392_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5391_);
                    crate::leanh::lean_dec_ref(v_H_5390_);
                    crate::leanh::lean_dec_ref(v_head_5389_);
                    crate::leanh::lean_dec(v_goal_5388_);
                    v___x_5559_ = crate::leanh::lean_box(0);
                    if v_isShared_5417_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5416_, 0, v___x_5559_);
                        v___x_5561_ = v___x_5416_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_5562_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5562_, 0, v___x_5559_);
                        v___x_5561_ = v_reuseFailAlloc_5562_;
                        state = 24;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5422_ = l_Lean_Meta_Context_config(v_a_5408_);
                v_foApprox_5423_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 0 as u32);
                v_ctxApprox_5424_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 1 as u32);
                v_quasiPatternApprox_5425_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_5422_, 2 as u32);
                v_constApprox_5426_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 3 as u32);
                v_isDefEqStuckEx_5427_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 4 as u32);
                v_unificationHints_5428_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 5 as u32);
                v_proofIrrelevance_5429_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 6 as u32);
                v_assignSyntheticOpaque_5430_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_5422_, 7 as u32);
                v_offsetCnstrs_5431_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 8 as u32);
                v_etaStruct_5432_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 10 as u32);
                v_univApprox_5433_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 11 as u32);
                v_iota_5434_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 12 as u32);
                v_beta_5435_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 13 as u32);
                v_proj_5436_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 14 as u32);
                v_zeta_5437_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 15 as u32);
                v_zetaDelta_5438_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 16 as u32);
                v_zetaUnused_5439_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 17 as u32);
                v_zetaHave_5440_ = crate::leanh::lean_ctor_get_uint8(v___x_5422_, 18 as u32);
                v_isSharedCheck_5557_ = (!crate::leanh::lean_is_exclusive(v___x_5422_)) as u8;
                if v_isSharedCheck_5557_ == 0 {
                    v___x_5442_ = v___x_5422_;
                    v_isShared_5443_ = v_isSharedCheck_5557_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5422_);
                    v___x_5442_ = crate::leanh::lean_box(0);
                    v_isShared_5443_ = v_isSharedCheck_5557_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_trackZetaDelta_5444_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5408_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5445_ = crate::leanh::lean_ctor_get(v_a_5408_, 1);
                v_lctx_5446_ = crate::leanh::lean_ctor_get(v_a_5408_, 2);
                v_localInstances_5447_ = crate::leanh::lean_ctor_get(v_a_5408_, 3);
                v_defEqCtx_x3f_5448_ = crate::leanh::lean_ctor_get(v_a_5408_, 4);
                v_synthPendingDepth_5449_ = crate::leanh::lean_ctor_get(v_a_5408_, 5);
                v_canUnfold_x3f_5450_ = crate::leanh::lean_ctor_get(v_a_5408_, 6);
                v_univApprox_5451_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5408_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5452_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5408_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5453_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5408_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5454_ = 2;
                if v_isShared_5443_ == 0 {
                    v_config_5456_ = v___x_5442_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5556_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        0 as u32,
                        v_foApprox_5423_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        1 as u32,
                        v_ctxApprox_5424_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        2 as u32,
                        v_quasiPatternApprox_5425_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        3 as u32,
                        v_constApprox_5426_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        4 as u32,
                        v_isDefEqStuckEx_5427_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        5 as u32,
                        v_unificationHints_5428_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        6 as u32,
                        v_proofIrrelevance_5429_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        7 as u32,
                        v_assignSyntheticOpaque_5430_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        8 as u32,
                        v_offsetCnstrs_5431_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        10 as u32,
                        v_etaStruct_5432_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        11 as u32,
                        v_univApprox_5433_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        12 as u32,
                        v_iota_5434_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        13 as u32,
                        v_beta_5435_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        14 as u32,
                        v_proj_5436_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        15 as u32,
                        v_zeta_5437_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        16 as u32,
                        v_zetaDelta_5438_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        17 as u32,
                        v_zetaUnused_5439_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        18 as u32,
                        v_zetaHave_5440_,
                    );
                    v_config_5456_ = v_reuseFailAlloc_5556_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(v_config_5456_, 9 as u32, v___x_5454_);
                v___x_5457_ = l_Lean_Meta_Context_configKey(v_a_5408_);
                v___x_5458_ = 3u64;
                v___x_5459_ = lean_uint64_shift_right(v___x_5457_, v___x_5458_);
                v___x_5460_ = lean_uint64_shift_left(v___x_5459_, v___x_5458_);
                v___x_5461_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0);
                v_key_5462_ = lean_uint64_lor(v___x_5460_, v___x_5461_);
                v___x_5463_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_5463_, 0, v_config_5456_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_5463_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_5462_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_5450_);
                crate::leanh::lean_inc(v_synthPendingDepth_5449_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_5448_);
                crate::leanh::lean_inc_ref(v_localInstances_5447_);
                crate::leanh::lean_inc_ref(v_lctx_5446_);
                crate::leanh::lean_inc(v_zetaDeltaSet_5445_);
                v___x_5464_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_5464_, 0, v___x_5463_);
                crate::leanh::lean_ctor_set(v___x_5464_, 1, v_zetaDeltaSet_5445_);
                crate::leanh::lean_ctor_set(v___x_5464_, 2, v_lctx_5446_);
                crate::leanh::lean_ctor_set(v___x_5464_, 3, v_localInstances_5447_);
                crate::leanh::lean_ctor_set(v___x_5464_, 4, v_defEqCtx_x3f_5448_);
                crate::leanh::lean_ctor_set(v___x_5464_, 5, v_synthPendingDepth_5449_);
                crate::leanh::lean_ctor_set(v___x_5464_, 6, v_canUnfold_x3f_5450_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5464_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5444_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5464_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5451_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5464_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5452_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5464_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5453_,
                );
                v___x_5465_ = l_Lean_Meta_reduceRecMatcher_x3f(
                    v_e_5399_,
                    v___x_5464_,
                    v_a_5409_,
                    v_a_5410_,
                    v_a_5411_,
                );
                crate::leanh::lean_dec_ref_known(v___x_5464_, 7);
                if crate::leanh::lean_obj_tag(v___x_5465_) == 0 {
                    v_a_5466_ = crate::leanh::lean_ctor_get(v___x_5465_, 0);
                    crate::leanh::lean_inc(v_a_5466_);
                    crate::leanh::lean_dec_ref_known(v___x_5465_, 1);
                    if crate::leanh::lean_obj_tag(v_a_5466_) == 1 {
                        crate::leanh::lean_del_object(v___x_5420_);
                        crate::leanh::lean_dec(v_val_5418_);
                        crate::leanh::lean_dec_ref(v_excessArgs_5400_);
                        crate::leanh::lean_dec_ref(v_e_5399_);
                        v_val_5467_ = crate::leanh::lean_ctor_get(v_a_5466_, 0);
                        v_isSharedCheck_5503_ = (!crate::leanh::lean_is_exclusive(v_a_5466_)) as u8;
                        if v_isSharedCheck_5503_ == 0 {
                            v___x_5469_ = v_a_5466_;
                            v_isShared_5470_ = v_isSharedCheck_5503_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5467_);
                            crate::leanh::lean_dec(v_a_5466_);
                            v___x_5469_ = crate::leanh::lean_box(0);
                            v_isShared_5470_ = v_isSharedCheck_5503_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5466_);
                        crate::leanh::lean_dec_ref(v_00_u03b1_5398_);
                        crate::leanh::lean_dec_ref(v_wpConst_5394_);
                        crate::leanh::lean_dec_ref(v_args_5393_);
                        crate::leanh::lean_dec_ref(v_ent_5392_);
                        crate::leanh::lean_dec_ref(v_H_5390_);
                        crate::leanh::lean_dec_ref(v_head_5389_);
                        v___x_5504_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(v_val_5418_, v_m_5395_, v_00_u03c3s_5391_, v_ps_5396_, v_instWP_5397_, v_excessArgs_5400_, v_a_5402_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
                        if crate::leanh::lean_obj_tag(v___x_5504_) == 0 {
                            v_a_5505_ = crate::leanh::lean_ctor_get(v___x_5504_, 0);
                            crate::leanh::lean_inc(v_a_5505_);
                            crate::leanh::lean_dec_ref_known(v___x_5504_, 1);
                            v___x_5506_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2);
                            v___x_5507_ = l_Lean_indentExpr(v_e_5399_);
                            crate::leanh::lean_inc_ref(v___x_5507_);
                            v___x_5508_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5508_, 0, v___x_5506_);
                            crate::leanh::lean_ctor_set(v___x_5508_, 1, v___x_5507_);
                            if v_isShared_5421_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5420_, 0, v___x_5508_);
                                v___x_5510_ = v___x_5420_;
                                state = 13;
                                continue;
                            } else {
                                v_reuseFailAlloc_5539_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5508_);
                                v___x_5510_ = v_reuseFailAlloc_5539_;
                                state = 13;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5420_);
                            crate::leanh::lean_dec_ref(v_e_5399_);
                            crate::leanh::lean_dec(v_goal_5388_);
                            v_a_5540_ = crate::leanh::lean_ctor_get(v___x_5504_, 0);
                            v_isSharedCheck_5547_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5504_)) as u8;
                            if v_isSharedCheck_5547_ == 0 {
                                v___x_5542_ = v___x_5504_;
                                v_isShared_5543_ = v_isSharedCheck_5547_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5540_);
                                crate::leanh::lean_dec(v___x_5504_);
                                v___x_5542_ = crate::leanh::lean_box(0);
                                v_isShared_5543_ = v_isSharedCheck_5547_;
                                state = 20;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5420_);
                    crate::leanh::lean_dec(v_val_5418_);
                    crate::leanh::lean_dec_ref(v_excessArgs_5400_);
                    crate::leanh::lean_dec_ref(v_e_5399_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5398_);
                    crate::leanh::lean_dec_ref(v_instWP_5397_);
                    crate::leanh::lean_dec_ref(v_ps_5396_);
                    crate::leanh::lean_dec_ref(v_m_5395_);
                    crate::leanh::lean_dec_ref(v_wpConst_5394_);
                    crate::leanh::lean_dec_ref(v_args_5393_);
                    crate::leanh::lean_dec_ref(v_ent_5392_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5391_);
                    crate::leanh::lean_dec_ref(v_H_5390_);
                    crate::leanh::lean_dec_ref(v_head_5389_);
                    crate::leanh::lean_dec(v_goal_5388_);
                    v_a_5548_ = crate::leanh::lean_ctor_get(v___x_5465_, 0);
                    v_isSharedCheck_5555_ = (!crate::leanh::lean_is_exclusive(v___x_5465_)) as u8;
                    if v_isSharedCheck_5555_ == 0 {
                        v___x_5550_ = v___x_5465_;
                        v_isShared_5551_ = v_isSharedCheck_5555_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5548_);
                        crate::leanh::lean_dec(v___x_5465_);
                        v___x_5550_ = crate::leanh::lean_box(0);
                        v_isShared_5551_ = v_isSharedCheck_5555_;
                        state = 22;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5471_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_5467_, v_a_5407_);
                if crate::leanh::lean_obj_tag(v___x_5471_) == 0 {
                    v_a_5472_ = crate::leanh::lean_ctor_get(v___x_5471_, 0);
                    crate::leanh::lean_inc(v_a_5472_);
                    crate::leanh::lean_dec_ref_known(v___x_5471_, 1);
                    v___x_5473_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_5388_, v_head_5389_, v_H_5390_, v_00_u03c3s_5391_, v_ent_5392_, v_args_5393_, v_wpConst_5394_, v_m_5395_, v_ps_5396_, v_instWP_5397_, v_00_u03b1_5398_, v_a_5472_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
                    if crate::leanh::lean_obj_tag(v___x_5473_) == 0 {
                        v_a_5474_ = crate::leanh::lean_ctor_get(v___x_5473_, 0);
                        v_isSharedCheck_5486_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5473_)) as u8;
                        if v_isSharedCheck_5486_ == 0 {
                            v___x_5476_ = v___x_5473_;
                            v_isShared_5477_ = v_isSharedCheck_5486_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5474_);
                            crate::leanh::lean_dec(v___x_5473_);
                            v___x_5476_ = crate::leanh::lean_box(0);
                            v_isShared_5477_ = v_isSharedCheck_5486_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5469_);
                        v_a_5487_ = crate::leanh::lean_ctor_get(v___x_5473_, 0);
                        v_isSharedCheck_5494_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5473_)) as u8;
                        if v_isSharedCheck_5494_ == 0 {
                            v___x_5489_ = v___x_5473_;
                            v_isShared_5490_ = v_isSharedCheck_5494_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5487_);
                            crate::leanh::lean_dec(v___x_5473_);
                            v___x_5489_ = crate::leanh::lean_box(0);
                            v_isShared_5490_ = v_isSharedCheck_5494_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5469_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5398_);
                    crate::leanh::lean_dec_ref(v_instWP_5397_);
                    crate::leanh::lean_dec_ref(v_ps_5396_);
                    crate::leanh::lean_dec_ref(v_m_5395_);
                    crate::leanh::lean_dec_ref(v_wpConst_5394_);
                    crate::leanh::lean_dec_ref(v_args_5393_);
                    crate::leanh::lean_dec_ref(v_ent_5392_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5391_);
                    crate::leanh::lean_dec_ref(v_H_5390_);
                    crate::leanh::lean_dec_ref(v_head_5389_);
                    crate::leanh::lean_dec(v_goal_5388_);
                    v_a_5495_ = crate::leanh::lean_ctor_get(v___x_5471_, 0);
                    v_isSharedCheck_5502_ = (!crate::leanh::lean_is_exclusive(v___x_5471_)) as u8;
                    if v_isSharedCheck_5502_ == 0 {
                        v___x_5497_ = v___x_5471_;
                        v_isShared_5498_ = v_isSharedCheck_5502_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5495_);
                        crate::leanh::lean_dec(v___x_5471_);
                        v___x_5497_ = crate::leanh::lean_box(0);
                        v_isShared_5498_ = v_isSharedCheck_5502_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5478_ = crate::leanh::lean_box(0);
                v___x_5479_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5479_, 0, v_a_5474_);
                crate::leanh::lean_ctor_set(v___x_5479_, 1, v___x_5478_);
                if v_isShared_5470_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5469_, 0, v___x_5479_);
                    v___x_5481_ = v___x_5469_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5485_, 0, v___x_5479_);
                    v___x_5481_ = v_reuseFailAlloc_5485_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5476_, 0, v___x_5481_);
                    v___x_5483_ = v___x_5476_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5484_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5481_);
                    v___x_5483_ = v_reuseFailAlloc_5484_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5483_;
            }
            9 => {
                if v_isShared_5490_ == 0 {
                    v___x_5492_ = v___x_5489_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
                    v___x_5492_ = v_reuseFailAlloc_5493_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5492_;
            }
            11 => {
                if v_isShared_5498_ == 0 {
                    v___x_5500_ = v___x_5497_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5495_);
                    v___x_5500_ = v_reuseFailAlloc_5501_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5500_;
            }
            13 => {
                v___x_5511_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_a_5505_,
                        v_goal_5388_,
                        v___x_5510_,
                        v_a_5401_,
                        v_a_5402_,
                        v_a_5403_,
                        v_a_5404_,
                        v_a_5405_,
                        v_a_5406_,
                        v_a_5407_,
                        v_a_5408_,
                        v_a_5409_,
                        v_a_5410_,
                        v_a_5411_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5511_) == 0 {
                    v_a_5512_ = crate::leanh::lean_ctor_get(v___x_5511_, 0);
                    v_isSharedCheck_5530_ = (!crate::leanh::lean_is_exclusive(v___x_5511_)) as u8;
                    if v_isSharedCheck_5530_ == 0 {
                        v___x_5514_ = v___x_5511_;
                        v_isShared_5515_ = v_isSharedCheck_5530_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5512_);
                        crate::leanh::lean_dec(v___x_5511_);
                        v___x_5514_ = crate::leanh::lean_box(0);
                        v_isShared_5515_ = v_isSharedCheck_5530_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5507_);
                    v_a_5531_ = crate::leanh::lean_ctor_get(v___x_5511_, 0);
                    v_isSharedCheck_5538_ = (!crate::leanh::lean_is_exclusive(v___x_5511_)) as u8;
                    if v_isSharedCheck_5538_ == 0 {
                        v___x_5533_ = v___x_5511_;
                        v_isShared_5534_ = v_isSharedCheck_5538_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5531_);
                        crate::leanh::lean_dec(v___x_5511_);
                        v___x_5533_ = crate::leanh::lean_box(0);
                        v_isShared_5534_ = v_isSharedCheck_5538_;
                        state = 18;
                        continue;
                    }
                }
            }
            14 => {
                if crate::leanh::lean_obj_tag(v_a_5512_) == 1 {
                    crate::leanh::lean_dec_ref(v___x_5507_);
                    v_mvarIds_5516_ = crate::leanh::lean_ctor_get(v_a_5512_, 0);
                    v_isSharedCheck_5526_ = (!crate::leanh::lean_is_exclusive(v_a_5512_)) as u8;
                    if v_isSharedCheck_5526_ == 0 {
                        v___x_5518_ = v_a_5512_;
                        v_isShared_5519_ = v_isSharedCheck_5526_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarIds_5516_);
                        crate::leanh::lean_dec(v_a_5512_);
                        v___x_5518_ = crate::leanh::lean_box(0);
                        v_isShared_5519_ = v_isSharedCheck_5526_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5514_);
                    crate::leanh::lean_dec(v_a_5512_);
                    v___x_5527_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4);
                    v___x_5528_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5528_, 0, v___x_5527_);
                    crate::leanh::lean_ctor_set(v___x_5528_, 1, v___x_5507_);
                    v___x_5529_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_5528_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
                    return v___x_5529_;
                }
            }
            15 => {
                if v_isShared_5519_ == 0 {
                    v___x_5521_ = v___x_5518_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_mvarIds_5516_);
                    v___x_5521_ = v_reuseFailAlloc_5525_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_5515_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5514_, 0, v___x_5521_);
                    v___x_5523_ = v___x_5514_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5524_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5521_);
                    v___x_5523_ = v_reuseFailAlloc_5524_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5523_;
            }
            18 => {
                if v_isShared_5534_ == 0 {
                    v___x_5536_ = v___x_5533_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5537_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_a_5531_);
                    v___x_5536_ = v_reuseFailAlloc_5537_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5536_;
            }
            20 => {
                if v_isShared_5543_ == 0 {
                    v___x_5545_ = v___x_5542_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5546_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
                    v___x_5545_ = v_reuseFailAlloc_5546_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5545_;
            }
            22 => {
                if v_isShared_5551_ == 0 {
                    v___x_5553_ = v___x_5550_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5554_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_a_5548_);
                    v___x_5553_ = v_reuseFailAlloc_5554_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5553_;
            }
            24 => {
                return v___x_5561_;
            }
            25 => {
                if v_isShared_5567_ == 0 {
                    v___x_5569_ = v___x_5566_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_a_5564_);
                    v___x_5569_ = v_reuseFailAlloc_5570_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_goal_5572_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_head_5573_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_H_5574_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_5575_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ent_5576_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_args_5577_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_wpConst_5578_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_m_5579_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_ps_5580_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_instWP_5581_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_00_u03b1_5582_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_e_5583_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_excessArgs_5584_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_5585_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_5586_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_5587_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_5588_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_5589_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_5590_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_a_5591_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_a_5592_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_a_5593_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_a_5594_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_a_5595_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v_a_5596_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v_res_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5597_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(v_goal_5572_, v_head_5573_, v_H_5574_, v_00_u03c3s_5575_, v_ent_5576_, v_args_5577_, v_wpConst_5578_, v_m_5579_, v_ps_5580_, v_instWP_5581_, v_00_u03b1_5582_, v_e_5583_, v_excessArgs_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
    crate::leanh::lean_dec(v_a_5595_);
    crate::leanh::lean_dec_ref(v_a_5594_);
    crate::leanh::lean_dec(v_a_5593_);
    crate::leanh::lean_dec_ref(v_a_5592_);
    crate::leanh::lean_dec(v_a_5591_);
    crate::leanh::lean_dec_ref(v_a_5590_);
    crate::leanh::lean_dec(v_a_5589_);
    crate::leanh::lean_dec_ref(v_a_5588_);
    crate::leanh::lean_dec(v_a_5587_);
    crate::leanh::lean_dec(v_a_5586_);
    crate::leanh::lean_dec_ref(v_a_5585_);
    return v_res_5597_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5599_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0;
    v___x_5600_ = l_Lean_stringToMessageData(v___x_5599_);
    return v___x_5600_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(
    mut v_goal_5601_: *mut crate::leanh::LeanObject,
    mut v_head_5602_: *mut crate::leanh::LeanObject,
    mut v_H_5603_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5604_: *mut crate::leanh::LeanObject,
    mut v_ent_5605_: *mut crate::leanh::LeanObject,
    mut v_args_5606_: *mut crate::leanh::LeanObject,
    mut v_wpConst_5607_: *mut crate::leanh::LeanObject,
    mut v_m_5608_: *mut crate::leanh::LeanObject,
    mut v_ps_5609_: *mut crate::leanh::LeanObject,
    mut v_instWP_5610_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5611_: *mut crate::leanh::LeanObject,
    mut v_e_5612_: *mut crate::leanh::LeanObject,
    mut v_f_5613_: *mut crate::leanh::LeanObject,
    mut v_a_5614_: *mut crate::leanh::LeanObject,
    mut v_a_5615_: *mut crate::leanh::LeanObject,
    mut v_a_5616_: *mut crate::leanh::LeanObject,
    mut v_a_5617_: *mut crate::leanh::LeanObject,
    mut v_a_5618_: *mut crate::leanh::LeanObject,
    mut v_a_5619_: *mut crate::leanh::LeanObject,
    mut v_a_5620_: *mut crate::leanh::LeanObject,
    mut v_a_5621_: *mut crate::leanh::LeanObject,
    mut v_a_5622_: *mut crate::leanh::LeanObject,
    mut v_a_5623_: *mut crate::leanh::LeanObject,
    mut v_a_5624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: u8 = 0;
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5633_: u8 = 0;
    let mut v_val_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5637_: u8 = 0;
    let mut v___y_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5660_: u8 = 0;
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v_a_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut v_a_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5679_: u8 = 0;
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5683_: u8 = 0;
    let mut v_options_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5685_: u8 = 0;
    let mut v_inheritedTraceOptions_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: u8 = 0;
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5703_: u8 = 0;
    let mut v_a_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5707_: u8 = 0;
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5711_: u8 = 0;
    let mut v_isSharedCheck_5712_: u8 = 0;
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5717_: u8 = 0;
    let mut v_a_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5725_: u8 = 0;
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5626_ = l_Lean_Expr_fvarId_x3f(v_f_5613_);
                if crate::leanh::lean_obj_tag(v___x_5626_) == 1 {
                    v_val_5627_ = crate::leanh::lean_ctor_get(v___x_5626_, 0);
                    crate::leanh::lean_inc_n(v_val_5627_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5626_, 1);
                    v___x_5628_ = 0;
                    v___x_5629_ = l_Lean_FVarId_getValue_x3f___redArg(
                        v_val_5627_,
                        v___x_5628_,
                        v_a_5621_,
                        v_a_5623_,
                        v_a_5624_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5629_) == 0 {
                        v_a_5630_ = crate::leanh::lean_ctor_get(v___x_5629_, 0);
                        v_isSharedCheck_5717_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5629_)) as u8;
                        if v_isSharedCheck_5717_ == 0 {
                            v___x_5632_ = v___x_5629_;
                            v_isShared_5633_ = v_isSharedCheck_5717_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5630_);
                            crate::leanh::lean_dec(v___x_5629_);
                            v___x_5632_ = crate::leanh::lean_box(0);
                            v_isShared_5633_ = v_isSharedCheck_5717_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5627_);
                        crate::leanh::lean_dec_ref(v_e_5612_);
                        crate::leanh::lean_dec_ref(v_00_u03b1_5611_);
                        crate::leanh::lean_dec_ref(v_instWP_5610_);
                        crate::leanh::lean_dec_ref(v_ps_5609_);
                        crate::leanh::lean_dec_ref(v_m_5608_);
                        crate::leanh::lean_dec_ref(v_wpConst_5607_);
                        crate::leanh::lean_dec_ref(v_args_5606_);
                        crate::leanh::lean_dec_ref(v_ent_5605_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_5604_);
                        crate::leanh::lean_dec_ref(v_H_5603_);
                        crate::leanh::lean_dec_ref(v_head_5602_);
                        crate::leanh::lean_dec(v_goal_5601_);
                        v_a_5718_ = crate::leanh::lean_ctor_get(v___x_5629_, 0);
                        v_isSharedCheck_5725_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5629_)) as u8;
                        if v_isSharedCheck_5725_ == 0 {
                            v___x_5720_ = v___x_5629_;
                            v_isShared_5721_ = v_isSharedCheck_5725_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5718_);
                            crate::leanh::lean_dec(v___x_5629_);
                            v___x_5720_ = crate::leanh::lean_box(0);
                            v_isShared_5721_ = v_isSharedCheck_5725_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5626_);
                    crate::leanh::lean_dec_ref(v_e_5612_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5611_);
                    crate::leanh::lean_dec_ref(v_instWP_5610_);
                    crate::leanh::lean_dec_ref(v_ps_5609_);
                    crate::leanh::lean_dec_ref(v_m_5608_);
                    crate::leanh::lean_dec_ref(v_wpConst_5607_);
                    crate::leanh::lean_dec_ref(v_args_5606_);
                    crate::leanh::lean_dec_ref(v_ent_5605_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5604_);
                    crate::leanh::lean_dec_ref(v_H_5603_);
                    crate::leanh::lean_dec_ref(v_head_5602_);
                    crate::leanh::lean_dec(v_goal_5601_);
                    v___x_5726_ = crate::leanh::lean_box(0);
                    v___x_5727_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5727_, 0, v___x_5726_);
                    return v___x_5727_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5630_) == 1 {
                    crate::leanh::lean_del_object(v___x_5632_);
                    v_val_5634_ = crate::leanh::lean_ctor_get(v_a_5630_, 0);
                    v_isSharedCheck_5712_ = (!crate::leanh::lean_is_exclusive(v_a_5630_)) as u8;
                    if v_isSharedCheck_5712_ == 0 {
                        v___x_5636_ = v_a_5630_;
                        v_isShared_5637_ = v_isSharedCheck_5712_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5634_);
                        crate::leanh::lean_dec(v_a_5630_);
                        v___x_5636_ = crate::leanh::lean_box(0);
                        v_isShared_5637_ = v_isSharedCheck_5712_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5630_);
                    crate::leanh::lean_dec(v_val_5627_);
                    crate::leanh::lean_dec_ref(v_e_5612_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5611_);
                    crate::leanh::lean_dec_ref(v_instWP_5610_);
                    crate::leanh::lean_dec_ref(v_ps_5609_);
                    crate::leanh::lean_dec_ref(v_m_5608_);
                    crate::leanh::lean_dec_ref(v_wpConst_5607_);
                    crate::leanh::lean_dec_ref(v_args_5606_);
                    crate::leanh::lean_dec_ref(v_ent_5605_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5604_);
                    crate::leanh::lean_dec_ref(v_H_5603_);
                    crate::leanh::lean_dec_ref(v_head_5602_);
                    crate::leanh::lean_dec(v_goal_5601_);
                    v___x_5713_ = crate::leanh::lean_box(0);
                    if v_isShared_5633_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5632_, 0, v___x_5713_);
                        v___x_5715_ = v___x_5632_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_5716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 0, v___x_5713_);
                        v___x_5715_ = v_reuseFailAlloc_5716_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_options_5684_ = crate::leanh::lean_ctor_get(v_a_5623_, 2);
                v_hasTrace_5685_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_5684_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5685_ == 0 {
                    crate::leanh::lean_dec(v_val_5627_);
                    v___y_5639_ = v_a_5614_;
                    v___y_5640_ = v_a_5615_;
                    v___y_5641_ = v_a_5616_;
                    v___y_5642_ = v_a_5617_;
                    v___y_5643_ = v_a_5618_;
                    v___y_5644_ = v_a_5619_;
                    v___y_5645_ = v_a_5620_;
                    v___y_5646_ = v_a_5621_;
                    v___y_5647_ = v_a_5622_;
                    v___y_5648_ = v_a_5623_;
                    v___y_5649_ = v_a_5624_;
                    state = 3;
                    continue;
                } else {
                    v_inheritedTraceOptions_5686_ = crate::leanh::lean_ctor_get(v_a_5623_, 13);
                    v___x_5687_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                    v___x_5688_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
                    v___x_5689_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5686_,
                        v_options_5684_,
                        v___x_5688_,
                    );
                    if v___x_5689_ == 0 {
                        crate::leanh::lean_dec(v_val_5627_);
                        v___y_5639_ = v_a_5614_;
                        v___y_5640_ = v_a_5615_;
                        v___y_5641_ = v_a_5616_;
                        v___y_5642_ = v_a_5617_;
                        v___y_5643_ = v_a_5618_;
                        v___y_5644_ = v_a_5619_;
                        v___y_5645_ = v_a_5620_;
                        v___y_5646_ = v_a_5621_;
                        v___y_5647_ = v_a_5622_;
                        v___y_5648_ = v_a_5623_;
                        v___y_5649_ = v_a_5624_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5690_ = l_Lean_FVarId_getUserName___redArg(
                            v_val_5627_,
                            v_a_5621_,
                            v_a_5623_,
                            v_a_5624_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5690_) == 0 {
                            v_a_5691_ = crate::leanh::lean_ctor_get(v___x_5690_, 0);
                            crate::leanh::lean_inc(v_a_5691_);
                            crate::leanh::lean_dec_ref_known(v___x_5690_, 1);
                            v___x_5692_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1);
                            v___x_5693_ = l_Lean_MessageData_ofName(v_a_5691_);
                            v___x_5694_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5694_, 0, v___x_5692_);
                            crate::leanh::lean_ctor_set(v___x_5694_, 1, v___x_5693_);
                            v___x_5695_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_5687_, v___x_5694_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_);
                            if crate::leanh::lean_obj_tag(v___x_5695_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5695_, 1);
                                v___y_5639_ = v_a_5614_;
                                v___y_5640_ = v_a_5615_;
                                v___y_5641_ = v_a_5616_;
                                v___y_5642_ = v_a_5617_;
                                v___y_5643_ = v_a_5618_;
                                v___y_5644_ = v_a_5619_;
                                v___y_5645_ = v_a_5620_;
                                v___y_5646_ = v_a_5621_;
                                v___y_5647_ = v_a_5622_;
                                v___y_5648_ = v_a_5623_;
                                v___y_5649_ = v_a_5624_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_5636_);
                                crate::leanh::lean_dec(v_val_5634_);
                                crate::leanh::lean_dec_ref(v_e_5612_);
                                crate::leanh::lean_dec_ref(v_00_u03b1_5611_);
                                crate::leanh::lean_dec_ref(v_instWP_5610_);
                                crate::leanh::lean_dec_ref(v_ps_5609_);
                                crate::leanh::lean_dec_ref(v_m_5608_);
                                crate::leanh::lean_dec_ref(v_wpConst_5607_);
                                crate::leanh::lean_dec_ref(v_args_5606_);
                                crate::leanh::lean_dec_ref(v_ent_5605_);
                                crate::leanh::lean_dec_ref(v_00_u03c3s_5604_);
                                crate::leanh::lean_dec_ref(v_H_5603_);
                                crate::leanh::lean_dec_ref(v_head_5602_);
                                crate::leanh::lean_dec(v_goal_5601_);
                                v_a_5696_ = crate::leanh::lean_ctor_get(v___x_5695_, 0);
                                v_isSharedCheck_5703_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5695_)) as u8;
                                if v_isSharedCheck_5703_ == 0 {
                                    v___x_5698_ = v___x_5695_;
                                    v_isShared_5699_ = v_isSharedCheck_5703_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5696_);
                                    crate::leanh::lean_dec(v___x_5695_);
                                    v___x_5698_ = crate::leanh::lean_box(0);
                                    v_isShared_5699_ = v_isSharedCheck_5703_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5636_);
                            crate::leanh::lean_dec(v_val_5634_);
                            crate::leanh::lean_dec_ref(v_e_5612_);
                            crate::leanh::lean_dec_ref(v_00_u03b1_5611_);
                            crate::leanh::lean_dec_ref(v_instWP_5610_);
                            crate::leanh::lean_dec_ref(v_ps_5609_);
                            crate::leanh::lean_dec_ref(v_m_5608_);
                            crate::leanh::lean_dec_ref(v_wpConst_5607_);
                            crate::leanh::lean_dec_ref(v_args_5606_);
                            crate::leanh::lean_dec_ref(v_ent_5605_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_5604_);
                            crate::leanh::lean_dec_ref(v_H_5603_);
                            crate::leanh::lean_dec_ref(v_head_5602_);
                            crate::leanh::lean_dec(v_goal_5601_);
                            v_a_5704_ = crate::leanh::lean_ctor_get(v___x_5690_, 0);
                            v_isSharedCheck_5711_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5690_)) as u8;
                            if v_isSharedCheck_5711_ == 0 {
                                v___x_5706_ = v___x_5690_;
                                v_isShared_5707_ = v_isSharedCheck_5711_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5704_);
                                crate::leanh::lean_dec(v___x_5690_);
                                v___x_5706_ = crate::leanh::lean_box(0);
                                v_isShared_5707_ = v_isSharedCheck_5711_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_5650_ = l_Lean_Expr_getAppNumArgs(v_e_5612_);
                v___x_5651_ = lean_mk_empty_array_with_capacity(v___x_5650_);
                crate::leanh::lean_dec(v___x_5650_);
                v___x_5652_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_5612_, v___x_5651_);
                v___x_5653_ =
                    l_Lean_Expr_betaRev(v_val_5634_, v___x_5652_, v___x_5628_, v___x_5628_);
                crate::leanh::lean_dec_ref(v___x_5652_);
                v___x_5654_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_5653_, v___y_5645_);
                if crate::leanh::lean_obj_tag(v___x_5654_) == 0 {
                    v_a_5655_ = crate::leanh::lean_ctor_get(v___x_5654_, 0);
                    crate::leanh::lean_inc(v_a_5655_);
                    crate::leanh::lean_dec_ref_known(v___x_5654_, 1);
                    v___x_5656_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_5601_, v_head_5602_, v_H_5603_, v_00_u03c3s_5604_, v_ent_5605_, v_args_5606_, v_wpConst_5607_, v_m_5608_, v_ps_5609_, v_instWP_5610_, v_00_u03b1_5611_, v_a_5655_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
                    if crate::leanh::lean_obj_tag(v___x_5656_) == 0 {
                        v_a_5657_ = crate::leanh::lean_ctor_get(v___x_5656_, 0);
                        v_isSharedCheck_5667_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5656_)) as u8;
                        if v_isSharedCheck_5667_ == 0 {
                            v___x_5659_ = v___x_5656_;
                            v_isShared_5660_ = v_isSharedCheck_5667_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5657_);
                            crate::leanh::lean_dec(v___x_5656_);
                            v___x_5659_ = crate::leanh::lean_box(0);
                            v_isShared_5660_ = v_isSharedCheck_5667_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5636_);
                        v_a_5668_ = crate::leanh::lean_ctor_get(v___x_5656_, 0);
                        v_isSharedCheck_5675_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5656_)) as u8;
                        if v_isSharedCheck_5675_ == 0 {
                            v___x_5670_ = v___x_5656_;
                            v_isShared_5671_ = v_isSharedCheck_5675_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5668_);
                            crate::leanh::lean_dec(v___x_5656_);
                            v___x_5670_ = crate::leanh::lean_box(0);
                            v_isShared_5671_ = v_isSharedCheck_5675_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5636_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5611_);
                    crate::leanh::lean_dec_ref(v_instWP_5610_);
                    crate::leanh::lean_dec_ref(v_ps_5609_);
                    crate::leanh::lean_dec_ref(v_m_5608_);
                    crate::leanh::lean_dec_ref(v_wpConst_5607_);
                    crate::leanh::lean_dec_ref(v_args_5606_);
                    crate::leanh::lean_dec_ref(v_ent_5605_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5604_);
                    crate::leanh::lean_dec_ref(v_H_5603_);
                    crate::leanh::lean_dec_ref(v_head_5602_);
                    crate::leanh::lean_dec(v_goal_5601_);
                    v_a_5676_ = crate::leanh::lean_ctor_get(v___x_5654_, 0);
                    v_isSharedCheck_5683_ = (!crate::leanh::lean_is_exclusive(v___x_5654_)) as u8;
                    if v_isSharedCheck_5683_ == 0 {
                        v___x_5678_ = v___x_5654_;
                        v_isShared_5679_ = v_isSharedCheck_5683_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5676_);
                        crate::leanh::lean_dec(v___x_5654_);
                        v___x_5678_ = crate::leanh::lean_box(0);
                        v_isShared_5679_ = v_isSharedCheck_5683_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5637_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5636_, 0, v_a_5657_);
                    v___x_5662_ = v___x_5636_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5666_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_a_5657_);
                    v___x_5662_ = v_reuseFailAlloc_5666_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5660_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5659_, 0, v___x_5662_);
                    v___x_5664_ = v___x_5659_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5665_, 0, v___x_5662_);
                    v___x_5664_ = v_reuseFailAlloc_5665_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5664_;
            }
            7 => {
                if v_isShared_5671_ == 0 {
                    v___x_5673_ = v___x_5670_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5674_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
                    v___x_5673_ = v_reuseFailAlloc_5674_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5673_;
            }
            9 => {
                if v_isShared_5679_ == 0 {
                    v___x_5681_ = v___x_5678_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_a_5676_);
                    v___x_5681_ = v_reuseFailAlloc_5682_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5681_;
            }
            11 => {
                if v_isShared_5699_ == 0 {
                    v___x_5701_ = v___x_5698_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5696_);
                    v___x_5701_ = v_reuseFailAlloc_5702_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5701_;
            }
            13 => {
                if v_isShared_5707_ == 0 {
                    v___x_5709_ = v___x_5706_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5710_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5710_, 0, v_a_5704_);
                    v___x_5709_ = v_reuseFailAlloc_5710_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5709_;
            }
            15 => {
                return v___x_5715_;
            }
            16 => {
                if v_isShared_5721_ == 0 {
                    v___x_5723_ = v___x_5720_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5724_, 0, v_a_5718_);
                    v___x_5723_ = v_reuseFailAlloc_5724_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_goal_5728_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_head_5729_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_H_5730_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_5731_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ent_5732_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_args_5733_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_wpConst_5734_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_m_5735_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_ps_5736_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_instWP_5737_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_00_u03b1_5738_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_e_5739_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_f_5740_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_5741_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_5742_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_5743_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_5744_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_5745_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_5746_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_a_5747_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_a_5748_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_a_5749_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_a_5750_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_a_5751_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v_a_5752_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v_res_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5753_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(v_goal_5728_, v_head_5729_, v_H_5730_, v_00_u03c3s_5731_, v_ent_5732_, v_args_5733_, v_wpConst_5734_, v_m_5735_, v_ps_5736_, v_instWP_5737_, v_00_u03b1_5738_, v_e_5739_, v_f_5740_, v_a_5741_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_);
    crate::leanh::lean_dec(v_a_5751_);
    crate::leanh::lean_dec_ref(v_a_5750_);
    crate::leanh::lean_dec(v_a_5749_);
    crate::leanh::lean_dec_ref(v_a_5748_);
    crate::leanh::lean_dec(v_a_5747_);
    crate::leanh::lean_dec_ref(v_a_5746_);
    crate::leanh::lean_dec(v_a_5745_);
    crate::leanh::lean_dec_ref(v_a_5744_);
    crate::leanh::lean_dec(v_a_5743_);
    crate::leanh::lean_dec(v_a_5742_);
    crate::leanh::lean_dec_ref(v_a_5741_);
    crate::leanh::lean_dec_ref(v_f_5740_);
    return v_res_5753_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceProg(
    mut v_goal_5754_: *mut crate::leanh::LeanObject,
    mut v_head_5755_: *mut crate::leanh::LeanObject,
    mut v_H_5756_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5757_: *mut crate::leanh::LeanObject,
    mut v_ent_5758_: *mut crate::leanh::LeanObject,
    mut v_args_5759_: *mut crate::leanh::LeanObject,
    mut v_wpConst_5760_: *mut crate::leanh::LeanObject,
    mut v_m_5761_: *mut crate::leanh::LeanObject,
    mut v_ps_5762_: *mut crate::leanh::LeanObject,
    mut v_instWP_5763_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5764_: *mut crate::leanh::LeanObject,
    mut v_e_5765_: *mut crate::leanh::LeanObject,
    mut v_f_5766_: *mut crate::leanh::LeanObject,
    mut v_a_5767_: *mut crate::leanh::LeanObject,
    mut v_a_5768_: *mut crate::leanh::LeanObject,
    mut v_a_5769_: *mut crate::leanh::LeanObject,
    mut v_a_5770_: *mut crate::leanh::LeanObject,
    mut v_a_5771_: *mut crate::leanh::LeanObject,
    mut v_a_5772_: *mut crate::leanh::LeanObject,
    mut v_a_5773_: *mut crate::leanh::LeanObject,
    mut v_a_5774_: *mut crate::leanh::LeanObject,
    mut v_a_5775_: *mut crate::leanh::LeanObject,
    mut v_a_5776_: *mut crate::leanh::LeanObject,
    mut v_a_5777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5783_: u8 = 0;
    let mut v_val_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5792_: u8 = 0;
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5799_: u8 = 0;
    let mut v_a_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5803_: u8 = 0;
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5807_: u8 = 0;
    let mut v_isSharedCheck_5808_: u8 = 0;
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5813_: u8 = 0;
    let mut v_a_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5817_: u8 = 0;
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5821_: u8 = 0;
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_f_5766_) == 11 {
                    v___x_5779_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(
                        v_e_5765_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5779_) == 0 {
                        v_a_5780_ = crate::leanh::lean_ctor_get(v___x_5779_, 0);
                        v_isSharedCheck_5813_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5779_)) as u8;
                        if v_isSharedCheck_5813_ == 0 {
                            v___x_5782_ = v___x_5779_;
                            v_isShared_5783_ = v_isSharedCheck_5813_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5780_);
                            crate::leanh::lean_dec(v___x_5779_);
                            v___x_5782_ = crate::leanh::lean_box(0);
                            v_isShared_5783_ = v_isSharedCheck_5813_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_00_u03b1_5764_);
                        crate::leanh::lean_dec_ref(v_instWP_5763_);
                        crate::leanh::lean_dec_ref(v_ps_5762_);
                        crate::leanh::lean_dec_ref(v_m_5761_);
                        crate::leanh::lean_dec_ref(v_wpConst_5760_);
                        crate::leanh::lean_dec_ref(v_args_5759_);
                        crate::leanh::lean_dec_ref(v_ent_5758_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_5757_);
                        crate::leanh::lean_dec_ref(v_H_5756_);
                        crate::leanh::lean_dec_ref(v_head_5755_);
                        crate::leanh::lean_dec(v_goal_5754_);
                        v_a_5814_ = crate::leanh::lean_ctor_get(v___x_5779_, 0);
                        v_isSharedCheck_5821_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5779_)) as u8;
                        if v_isSharedCheck_5821_ == 0 {
                            v___x_5816_ = v___x_5779_;
                            v_isShared_5817_ = v_isSharedCheck_5821_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5814_);
                            crate::leanh::lean_dec(v___x_5779_);
                            v___x_5816_ = crate::leanh::lean_box(0);
                            v_isShared_5817_ = v_isSharedCheck_5821_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5765_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5764_);
                    crate::leanh::lean_dec_ref(v_instWP_5763_);
                    crate::leanh::lean_dec_ref(v_ps_5762_);
                    crate::leanh::lean_dec_ref(v_m_5761_);
                    crate::leanh::lean_dec_ref(v_wpConst_5760_);
                    crate::leanh::lean_dec_ref(v_args_5759_);
                    crate::leanh::lean_dec_ref(v_ent_5758_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5757_);
                    crate::leanh::lean_dec_ref(v_H_5756_);
                    crate::leanh::lean_dec_ref(v_head_5755_);
                    crate::leanh::lean_dec(v_goal_5754_);
                    v___x_5822_ = crate::leanh::lean_box(0);
                    v___x_5823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5823_, 0, v___x_5822_);
                    return v___x_5823_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5780_) == 1 {
                    crate::leanh::lean_del_object(v___x_5782_);
                    v_val_5784_ = crate::leanh::lean_ctor_get(v_a_5780_, 0);
                    v_isSharedCheck_5808_ = (!crate::leanh::lean_is_exclusive(v_a_5780_)) as u8;
                    if v_isSharedCheck_5808_ == 0 {
                        v___x_5786_ = v_a_5780_;
                        v_isShared_5787_ = v_isSharedCheck_5808_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5784_);
                        crate::leanh::lean_dec(v_a_5780_);
                        v___x_5786_ = crate::leanh::lean_box(0);
                        v_isShared_5787_ = v_isSharedCheck_5808_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5780_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_5764_);
                    crate::leanh::lean_dec_ref(v_instWP_5763_);
                    crate::leanh::lean_dec_ref(v_ps_5762_);
                    crate::leanh::lean_dec_ref(v_m_5761_);
                    crate::leanh::lean_dec_ref(v_wpConst_5760_);
                    crate::leanh::lean_dec_ref(v_args_5759_);
                    crate::leanh::lean_dec_ref(v_ent_5758_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5757_);
                    crate::leanh::lean_dec_ref(v_H_5756_);
                    crate::leanh::lean_dec_ref(v_head_5755_);
                    crate::leanh::lean_dec(v_goal_5754_);
                    v___x_5809_ = crate::leanh::lean_box(0);
                    if v_isShared_5783_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5782_, 0, v___x_5809_);
                        v___x_5811_ = v___x_5782_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5812_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5812_, 0, v___x_5809_);
                        v___x_5811_ = v_reuseFailAlloc_5812_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5788_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_5754_, v_head_5755_, v_H_5756_, v_00_u03c3s_5757_, v_ent_5758_, v_args_5759_, v_wpConst_5760_, v_m_5761_, v_ps_5762_, v_instWP_5763_, v_00_u03b1_5764_, v_val_5784_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_);
                if crate::leanh::lean_obj_tag(v___x_5788_) == 0 {
                    v_a_5789_ = crate::leanh::lean_ctor_get(v___x_5788_, 0);
                    v_isSharedCheck_5799_ = (!crate::leanh::lean_is_exclusive(v___x_5788_)) as u8;
                    if v_isSharedCheck_5799_ == 0 {
                        v___x_5791_ = v___x_5788_;
                        v_isShared_5792_ = v_isSharedCheck_5799_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5789_);
                        crate::leanh::lean_dec(v___x_5788_);
                        v___x_5791_ = crate::leanh::lean_box(0);
                        v_isShared_5792_ = v_isSharedCheck_5799_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5786_);
                    v_a_5800_ = crate::leanh::lean_ctor_get(v___x_5788_, 0);
                    v_isSharedCheck_5807_ = (!crate::leanh::lean_is_exclusive(v___x_5788_)) as u8;
                    if v_isSharedCheck_5807_ == 0 {
                        v___x_5802_ = v___x_5788_;
                        v_isShared_5803_ = v_isSharedCheck_5807_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5800_);
                        crate::leanh::lean_dec(v___x_5788_);
                        v___x_5802_ = crate::leanh::lean_box(0);
                        v_isShared_5803_ = v_isSharedCheck_5807_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5786_, 0, v_a_5789_);
                    v___x_5794_ = v___x_5786_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_a_5789_);
                    v___x_5794_ = v_reuseFailAlloc_5798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5792_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5791_, 0, v___x_5794_);
                    v___x_5796_ = v___x_5791_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5797_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5797_, 0, v___x_5794_);
                    v___x_5796_ = v_reuseFailAlloc_5797_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5796_;
            }
            6 => {
                if v_isShared_5803_ == 0 {
                    v___x_5805_ = v___x_5802_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_a_5800_);
                    v___x_5805_ = v_reuseFailAlloc_5806_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5805_;
            }
            8 => {
                return v___x_5811_;
            }
            9 => {
                if v_isShared_5817_ == 0 {
                    v___x_5819_ = v___x_5816_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5820_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_a_5814_);
                    v___x_5819_ = v_reuseFailAlloc_5820_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceProg___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_goal_5824_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_head_5825_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_H_5826_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_5827_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ent_5828_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_args_5829_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_wpConst_5830_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_m_5831_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_ps_5832_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_instWP_5833_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_00_u03b1_5834_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_e_5835_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_f_5836_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_5837_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_5838_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_5839_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_5840_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_5841_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_5842_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_a_5843_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_a_5844_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_a_5845_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_a_5846_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_a_5847_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v_a_5848_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v_res_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5849_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceProg(v_goal_5824_, v_head_5825_, v_H_5826_, v_00_u03c3s_5827_, v_ent_5828_, v_args_5829_, v_wpConst_5830_, v_m_5831_, v_ps_5832_, v_instWP_5833_, v_00_u03b1_5834_, v_e_5835_, v_f_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_);
    crate::leanh::lean_dec(v_a_5847_);
    crate::leanh::lean_dec_ref(v_a_5846_);
    crate::leanh::lean_dec(v_a_5845_);
    crate::leanh::lean_dec_ref(v_a_5844_);
    crate::leanh::lean_dec(v_a_5843_);
    crate::leanh::lean_dec_ref(v_a_5842_);
    crate::leanh::lean_dec(v_a_5841_);
    crate::leanh::lean_dec_ref(v_a_5840_);
    crate::leanh::lean_dec(v_a_5839_);
    crate::leanh::lean_dec(v_a_5838_);
    crate::leanh::lean_dec_ref(v_a_5837_);
    crate::leanh::lean_dec_ref(v_f_5836_);
    return v_res_5849_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(
    mut v_cls_5850_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5851_: *mut crate::leanh::LeanObject,
    mut v___y_5852_: *mut crate::leanh::LeanObject,
    mut v___y_5853_: *mut crate::leanh::LeanObject,
    mut v___y_5854_: *mut crate::leanh::LeanObject,
    mut v___y_5855_: *mut crate::leanh::LeanObject,
    mut v___y_5856_: *mut crate::leanh::LeanObject,
    mut v___y_5857_: *mut crate::leanh::LeanObject,
    mut v___y_5858_: *mut crate::leanh::LeanObject,
    mut v___y_5859_: *mut crate::leanh::LeanObject,
    mut v___y_5860_: *mut crate::leanh::LeanObject,
    mut v___y_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5865_: u8 = 0;
    v_options_5864_ = crate::leanh::lean_ctor_get(v___y_5861_, 2);
    v_hasTrace_5865_ = crate::leanh::lean_ctor_get_uint8(
        v_options_5864_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_5865_ == 0 {
        let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_cls_5850_);
        v___x_5866_ = crate::leanh::lean_box((v_hasTrace_5865_) as usize);
        v___x_5867_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5867_, 0, v___x_5866_);
        return v___x_5867_;
    } else {
        let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5870_: u8 = 0;
        let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5868_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8;
        v___x_5869_ = l_Lean_Name_append(v___x_5868_, v_cls_5850_);
        v___x_5870_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_5851_,
            v_options_5864_,
            v___x_5869_,
        );
        crate::leanh::lean_dec(v___x_5869_);
        v___x_5871_ = crate::leanh::lean_box((v___x_5870_) as usize);
        v___x_5872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5872_, 0, v___x_5871_);
        return v___x_5872_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed(
    mut v_cls_5873_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5874_: *mut crate::leanh::LeanObject,
    mut v___y_5875_: *mut crate::leanh::LeanObject,
    mut v___y_5876_: *mut crate::leanh::LeanObject,
    mut v___y_5877_: *mut crate::leanh::LeanObject,
    mut v___y_5878_: *mut crate::leanh::LeanObject,
    mut v___y_5879_: *mut crate::leanh::LeanObject,
    mut v___y_5880_: *mut crate::leanh::LeanObject,
    mut v___y_5881_: *mut crate::leanh::LeanObject,
    mut v___y_5882_: *mut crate::leanh::LeanObject,
    mut v___y_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5887_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(v_cls_5873_, v_____do__lift_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_);
    crate::leanh::lean_dec(v___y_5885_);
    crate::leanh::lean_dec_ref(v___y_5884_);
    crate::leanh::lean_dec(v___y_5883_);
    crate::leanh::lean_dec_ref(v___y_5882_);
    crate::leanh::lean_dec(v___y_5881_);
    crate::leanh::lean_dec_ref(v___y_5880_);
    crate::leanh::lean_dec(v___y_5879_);
    crate::leanh::lean_dec_ref(v___y_5878_);
    crate::leanh::lean_dec(v___y_5877_);
    crate::leanh::lean_dec(v___y_5876_);
    crate::leanh::lean_dec_ref(v___y_5875_);
    crate::leanh::lean_dec_ref(v_____do__lift_5874_);
    return v_res_5887_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(
    mut v_a_5888_: *mut crate::leanh::LeanObject,
    mut v_a_5889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5895_: u8 = 0;
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5888_) == 0 {
                    v___x_5890_ = l_List_reverse___redArg(v_a_5889_);
                    return v___x_5890_;
                } else {
                    v_head_5891_ = crate::leanh::lean_ctor_get(v_a_5888_, 0);
                    v_tail_5892_ = crate::leanh::lean_ctor_get(v_a_5888_, 1);
                    v_isSharedCheck_5901_ = (!crate::leanh::lean_is_exclusive(v_a_5888_)) as u8;
                    if v_isSharedCheck_5901_ == 0 {
                        v___x_5894_ = v_a_5888_;
                        v_isShared_5895_ = v_isSharedCheck_5901_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5892_);
                        crate::leanh::lean_inc(v_head_5891_);
                        crate::leanh::lean_dec(v_a_5888_);
                        v___x_5894_ = crate::leanh::lean_box(0);
                        v_isShared_5895_ = v_isSharedCheck_5901_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5896_ = l_Lean_MessageData_ofExpr(v_head_5891_);
                if v_isShared_5895_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5894_, 1, v_a_5889_);
                    crate::leanh::lean_ctor_set(v___x_5894_, 0, v___x_5896_);
                    v___x_5898_ = v___x_5894_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5900_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5900_, 0, v___x_5896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5900_, 1, v_a_5889_);
                    v___x_5898_ = v_reuseFailAlloc_5900_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5888_ = v_tail_5892_;
                v_a_5889_ = v___x_5898_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5903_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0;
    v___x_5904_ = l_Lean_stringToMessageData(v___x_5903_);
    return v___x_5904_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5906_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2;
    v___x_5907_ = l_Lean_stringToMessageData(v___x_5906_);
    return v___x_5907_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5909_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4;
    v___x_5910_ = l_Lean_stringToMessageData(v___x_5909_);
    return v___x_5910_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5912_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6;
    v___x_5913_ = l_Lean_stringToMessageData(v___x_5912_);
    return v___x_5913_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5915_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8;
    v___x_5916_ = l_Lean_stringToMessageData(v___x_5915_);
    return v___x_5916_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5918_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10;
    v___x_5919_ = l_Lean_stringToMessageData(v___x_5918_);
    return v___x_5919_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5921_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12;
    v___x_5922_ = l_Lean_stringToMessageData(v___x_5921_);
    return v___x_5922_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5924_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14;
    v___x_5925_ = l_Lean_stringToMessageData(v___x_5924_);
    return v___x_5925_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5927_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16;
    v___x_5928_ = l_Lean_stringToMessageData(v___x_5927_);
    return v___x_5928_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5930_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18;
    v___x_5931_ = l_Lean_stringToMessageData(v___x_5930_);
    return v___x_5931_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5933_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20;
    v___x_5934_ = l_Lean_stringToMessageData(v___x_5933_);
    return v___x_5934_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5938_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23;
    v___x_5939_ = l_Lean_stringToMessageData(v___x_5938_);
    return v___x_5939_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5941_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25;
    v___x_5942_ = l_Lean_stringToMessageData(v___x_5941_);
    return v___x_5942_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(
    mut v_scope_5943_: *mut crate::leanh::LeanObject,
    mut v_goal_5944_: *mut crate::leanh::LeanObject,
    mut v_e_5945_: *mut crate::leanh::LeanObject,
    mut v_excessArgs_5946_: *mut crate::leanh::LeanObject,
    mut v_m_5947_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5948_: *mut crate::leanh::LeanObject,
    mut v_ps_5949_: *mut crate::leanh::LeanObject,
    mut v_instWP_5950_: *mut crate::leanh::LeanObject,
    mut v_a_5951_: *mut crate::leanh::LeanObject,
    mut v_a_5952_: *mut crate::leanh::LeanObject,
    mut v_a_5953_: *mut crate::leanh::LeanObject,
    mut v_a_5954_: *mut crate::leanh::LeanObject,
    mut v_a_5955_: *mut crate::leanh::LeanObject,
    mut v_a_5956_: *mut crate::leanh::LeanObject,
    mut v_a_5957_: *mut crate::leanh::LeanObject,
    mut v_a_5958_: *mut crate::leanh::LeanObject,
    mut v_a_5959_: *mut crate::leanh::LeanObject,
    mut v_a_5960_: *mut crate::leanh::LeanObject,
    mut v_a_5961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5987_: u8 = 0;
    let mut v_mvarIds_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6004_: u8 = 0;
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6008_: u8 = 0;
    let mut v_isSharedCheck_6009_: u8 = 0;
    let mut v_a_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6013_: u8 = 0;
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6017_: u8 = 0;
    let mut v___y_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6042_: u8 = 0;
    let mut v_val_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: u8 = 0;
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6054_: u8 = 0;
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6058_: u8 = 0;
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: u8 = 0;
    let mut v_expr_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6075_: u8 = 0;
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6079_: u8 = 0;
    let mut v_a_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6083_: u8 = 0;
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6087_: u8 = 0;
    let mut v_a_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6091_: u8 = 0;
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6095_: u8 = 0;
    let mut v_a_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6099_: u8 = 0;
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6103_: u8 = 0;
    let mut v_a_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6107_: u8 = 0;
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6111_: u8 = 0;
    let mut v___y_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6134_: u8 = 0;
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut v___y_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_specs_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6158_: u8 = 0;
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6161_: u8 = 0;
    let mut v_a_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6169_: u8 = 0;
    let mut v_unused_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: u8 = 0;
    let mut v_proof_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6205_: u8 = 0;
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6209_: u8 = 0;
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v_a_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6214_: u8 = 0;
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6218_: u8 = 0;
    let mut v___y_6220_: u8 = 0;
    let mut v_inheritedTraceOptions_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: u8 = 0;
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6241_: u8 = 0;
    let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6245_: u8 = 0;
    let mut v_f_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: u8 = 0;
    let mut v___x_6248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_f_6246_ = l_Lean_Expr_getAppFn(v_e_5945_);
                v___x_6247_ = l_Lean_Expr_isConst(v_f_6246_);
                if v___x_6247_ == 0 {
                    v___x_6248_ = l_Lean_Expr_isFVar(v_f_6246_);
                    crate::leanh::lean_dec_ref(v_f_6246_);
                    v___y_6220_ = v___x_6248_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_6246_);
                    v___y_6220_ = v___x_6247_;
                    state = 35;
                    continue;
                }
            }
            1 => {
                v___x_5964_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5964_, 0, v_e_5945_);
                v___x_5965_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5965_, 0, v___x_5964_);
                return v___x_5965_;
            }
            2 => {
                v___x_5979_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
                v___x_5980_ = l_Lean_indentExpr(v_e_5945_);
                crate::leanh::lean_inc_ref(v___x_5980_);
                v___x_5981_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5981_, 0, v___x_5979_);
                crate::leanh::lean_ctor_set(v___x_5981_, 1, v___x_5980_);
                v___x_5982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5982_, 0, v___x_5981_);
                crate::leanh::lean_inc_ref(v___y_5967_);
                v___x_5983_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v___y_5967_,
                        v_goal_5944_,
                        v___x_5982_,
                        v___y_5968_,
                        v___y_5969_,
                        v___y_5970_,
                        v___y_5971_,
                        v___y_5972_,
                        v___y_5973_,
                        v___y_5974_,
                        v___y_5975_,
                        v___y_5976_,
                        v___y_5977_,
                        v___y_5978_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5983_) == 0 {
                    v_a_5984_ = crate::leanh::lean_ctor_get(v___x_5983_, 0);
                    v_isSharedCheck_6009_ = (!crate::leanh::lean_is_exclusive(v___x_5983_)) as u8;
                    if v_isSharedCheck_6009_ == 0 {
                        v___x_5986_ = v___x_5983_;
                        v_isShared_5987_ = v_isSharedCheck_6009_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5984_);
                        crate::leanh::lean_dec(v___x_5983_);
                        v___x_5986_ = crate::leanh::lean_box(0);
                        v_isShared_5987_ = v_isSharedCheck_6009_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5980_);
                    crate::leanh::lean_dec_ref(v___y_5967_);
                    crate::leanh::lean_dec_ref(v_scope_5943_);
                    v_a_6010_ = crate::leanh::lean_ctor_get(v___x_5983_, 0);
                    v_isSharedCheck_6017_ = (!crate::leanh::lean_is_exclusive(v___x_5983_)) as u8;
                    if v_isSharedCheck_6017_ == 0 {
                        v___x_6012_ = v___x_5983_;
                        v_isShared_6013_ = v_isSharedCheck_6017_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6010_);
                        crate::leanh::lean_dec(v___x_5983_);
                        v___x_6012_ = crate::leanh::lean_box(0);
                        v_isShared_6013_ = v_isSharedCheck_6017_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_5984_) == 1 {
                    crate::leanh::lean_dec_ref(v___x_5980_);
                    crate::leanh::lean_dec_ref(v___y_5967_);
                    v_mvarIds_5988_ = crate::leanh::lean_ctor_get(v_a_5984_, 0);
                    crate::leanh::lean_inc(v_mvarIds_5988_);
                    crate::leanh::lean_dec_ref_known(v_a_5984_, 1);
                    v___x_5989_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5989_, 0, v_scope_5943_);
                    crate::leanh::lean_ctor_set(v___x_5989_, 1, v_mvarIds_5988_);
                    if v_isShared_5987_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5986_, 0, v___x_5989_);
                        v___x_5991_ = v___x_5986_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5992_, 0, v___x_5989_);
                        v___x_5991_ = v_reuseFailAlloc_5992_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5986_);
                    crate::leanh::lean_dec(v_a_5984_);
                    crate::leanh::lean_dec_ref(v_scope_5943_);
                    v_expr_5993_ = crate::leanh::lean_ctor_get(v___y_5967_, 0);
                    crate::leanh::lean_inc_ref(v_expr_5993_);
                    crate::leanh::lean_dec_ref(v___y_5967_);
                    v___x_5994_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
                    v___x_5995_ = l_Lean_MessageData_ofExpr(v_expr_5993_);
                    v___x_5996_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5996_, 0, v___x_5994_);
                    crate::leanh::lean_ctor_set(v___x_5996_, 1, v___x_5995_);
                    v___x_5997_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
                    v___x_5998_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5998_, 0, v___x_5996_);
                    crate::leanh::lean_ctor_set(v___x_5998_, 1, v___x_5997_);
                    v___x_5999_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5999_, 0, v___x_5998_);
                    crate::leanh::lean_ctor_set(v___x_5999_, 1, v___x_5980_);
                    v___x_6000_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_5999_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
                    v_a_6001_ = crate::leanh::lean_ctor_get(v___x_6000_, 0);
                    v_isSharedCheck_6008_ = (!crate::leanh::lean_is_exclusive(v___x_6000_)) as u8;
                    if v_isSharedCheck_6008_ == 0 {
                        v___x_6003_ = v___x_6000_;
                        v_isShared_6004_ = v_isSharedCheck_6008_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6001_);
                        crate::leanh::lean_dec(v___x_6000_);
                        v___x_6003_ = crate::leanh::lean_box(0);
                        v_isShared_6004_ = v_isSharedCheck_6008_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5991_;
            }
            5 => {
                if v_isShared_6004_ == 0 {
                    v___x_6006_ = v___x_6003_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6007_, 0, v_a_6001_);
                    v___x_6006_ = v_reuseFailAlloc_6007_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6006_;
            }
            7 => {
                if v_isShared_6013_ == 0 {
                    v___x_6015_ = v___x_6012_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_a_6010_);
                    v___x_6015_ = v_reuseFailAlloc_6016_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6015_;
            }
            9 => {
                v___x_6020_ = crate::leanh::lean_box(0);
                v___x_6021_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6021_, 0, v___y_6019_);
                crate::leanh::lean_ctor_set(v___x_6021_, 1, v___x_6020_);
                v___x_6022_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6022_, 0, v_scope_5943_);
                crate::leanh::lean_ctor_set(v___x_6022_, 1, v___x_6021_);
                v___x_6023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6023_, 0, v___x_6022_);
                return v___x_6023_;
            }
            10 => {
                crate::leanh::lean_inc(v_goal_5944_);
                crate::leanh::lean_inc_ref(v___y_6026_);
                v___x_6039_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro(
                    v___y_6026_,
                    v_goal_5944_,
                    v_excessArgs_5946_,
                    v___y_6028_,
                    v___y_6029_,
                    v___y_6030_,
                    v___y_6031_,
                    v___y_6032_,
                    v___y_6033_,
                    v___y_6034_,
                    v___y_6035_,
                    v___y_6036_,
                    v___y_6037_,
                    v___y_6038_,
                );
                if crate::leanh::lean_obj_tag(v___x_6039_) == 0 {
                    v_a_6040_ = crate::leanh::lean_ctor_get(v___x_6039_, 0);
                    crate::leanh::lean_inc(v_a_6040_);
                    crate::leanh::lean_dec_ref_known(v___x_6039_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6040_) == 1 {
                        crate::leanh::lean_dec_ref(v___y_6026_);
                        crate::leanh::lean_dec_ref(v_instWP_5950_);
                        crate::leanh::lean_dec_ref(v_ps_5949_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_5948_);
                        crate::leanh::lean_dec_ref(v_m_5947_);
                        crate::leanh::lean_dec_ref(v_excessArgs_5946_);
                        crate::leanh::lean_dec_ref(v_e_5945_);
                        crate::leanh::lean_dec(v_goal_5944_);
                        v_options_6041_ = crate::leanh::lean_ctor_get(v___y_6037_, 2);
                        v_hasTrace_6042_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_6041_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_6042_ == 0 {
                            crate::leanh::lean_dec(v___y_6027_);
                            v_val_6043_ = crate::leanh::lean_ctor_get(v_a_6040_, 0);
                            crate::leanh::lean_inc(v_val_6043_);
                            crate::leanh::lean_dec_ref_known(v_a_6040_, 1);
                            v___y_6019_ = v_val_6043_;
                            state = 9;
                            continue;
                        } else {
                            v_val_6044_ = crate::leanh::lean_ctor_get(v_a_6040_, 0);
                            crate::leanh::lean_inc(v_val_6044_);
                            crate::leanh::lean_dec_ref_known(v_a_6040_, 1);
                            v_inheritedTraceOptions_6045_ =
                                crate::leanh::lean_ctor_get(v___y_6037_, 13);
                            v___x_6046_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8;
                            crate::leanh::lean_inc(v___y_6027_);
                            v___x_6047_ = l_Lean_Name_append(v___x_6046_, v___y_6027_);
                            v___x_6048_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_6045_,
                                v_options_6041_,
                                v___x_6047_,
                            );
                            crate::leanh::lean_dec(v___x_6047_);
                            if v___x_6048_ == 0 {
                                crate::leanh::lean_dec(v___y_6027_);
                                v___y_6019_ = v_val_6044_;
                                state = 9;
                                continue;
                            } else {
                                v___x_6049_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
                                v___x_6050_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_6027_, v___x_6049_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_);
                                if crate::leanh::lean_obj_tag(v___x_6050_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6050_, 1);
                                    v___y_6019_ = v_val_6044_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_val_6044_);
                                    crate::leanh::lean_dec_ref(v_scope_5943_);
                                    v_a_6051_ = crate::leanh::lean_ctor_get(v___x_6050_, 0);
                                    v_isSharedCheck_6058_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6050_)) as u8;
                                    if v_isSharedCheck_6058_ == 0 {
                                        v___x_6053_ = v___x_6050_;
                                        v_isShared_6054_ = v_isSharedCheck_6058_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6051_);
                                        crate::leanh::lean_dec(v___x_6050_);
                                        v___x_6053_ = crate::leanh::lean_box(0);
                                        v_isShared_6054_ = v_isSharedCheck_6058_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6040_);
                        v___x_6059_ =
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(
                                v___y_6026_,
                                v_m_5947_,
                                v_00_u03c3s_5948_,
                                v_ps_5949_,
                                v_instWP_5950_,
                                v_excessArgs_5946_,
                                v___y_6028_,
                                v___y_6029_,
                                v___y_6030_,
                                v___y_6031_,
                                v___y_6032_,
                                v___y_6033_,
                                v___y_6034_,
                                v___y_6035_,
                                v___y_6036_,
                                v___y_6037_,
                                v___y_6038_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_6059_) == 0 {
                            v_a_6060_ = crate::leanh::lean_ctor_get(v___x_6059_, 0);
                            crate::leanh::lean_inc(v_a_6060_);
                            crate::leanh::lean_dec_ref_known(v___x_6059_, 1);
                            v_inheritedTraceOptions_6061_ =
                                crate::leanh::lean_ctor_get(v___y_6037_, 13);
                            crate::leanh::lean_inc_ref(v___y_6025_);
                            crate::leanh::lean_inc(v___y_6038_);
                            crate::leanh::lean_inc_ref(v___y_6037_);
                            crate::leanh::lean_inc(v___y_6036_);
                            crate::leanh::lean_inc_ref(v___y_6035_);
                            crate::leanh::lean_inc(v___y_6034_);
                            crate::leanh::lean_inc_ref(v___y_6033_);
                            crate::leanh::lean_inc(v___y_6032_);
                            crate::leanh::lean_inc_ref(v___y_6031_);
                            crate::leanh::lean_inc(v___y_6030_);
                            crate::leanh::lean_inc(v___y_6029_);
                            crate::leanh::lean_inc_ref(v___y_6028_);
                            crate::leanh::lean_inc_ref(v_inheritedTraceOptions_6061_);
                            v___x_6062_ = crate::leanh::lean_apply_13(
                                v___y_6025_,
                                v_inheritedTraceOptions_6061_,
                                v___y_6028_,
                                v___y_6029_,
                                v___y_6030_,
                                v___y_6031_,
                                v___y_6032_,
                                v___y_6033_,
                                v___y_6034_,
                                v___y_6035_,
                                v___y_6036_,
                                v___y_6037_,
                                v___y_6038_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_6062_) == 0 {
                                v_a_6063_ = crate::leanh::lean_ctor_get(v___x_6062_, 0);
                                crate::leanh::lean_inc(v_a_6063_);
                                crate::leanh::lean_dec_ref_known(v___x_6062_, 1);
                                v___x_6064_ = (crate::leanh::lean_unbox(v_a_6063_) as u8);
                                crate::leanh::lean_dec(v_a_6063_);
                                if v___x_6064_ == 0 {
                                    crate::leanh::lean_dec(v___y_6027_);
                                    v___y_5967_ = v_a_6060_;
                                    v___y_5968_ = v___y_6028_;
                                    v___y_5969_ = v___y_6029_;
                                    v___y_5970_ = v___y_6030_;
                                    v___y_5971_ = v___y_6031_;
                                    v___y_5972_ = v___y_6032_;
                                    v___y_5973_ = v___y_6033_;
                                    v___y_5974_ = v___y_6034_;
                                    v___y_5975_ = v___y_6035_;
                                    v___y_5976_ = v___y_6036_;
                                    v___y_5977_ = v___y_6037_;
                                    v___y_5978_ = v___y_6038_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_expr_6065_ = crate::leanh::lean_ctor_get(v_a_6060_, 0);
                                    crate::leanh::lean_inc(v___y_6038_);
                                    crate::leanh::lean_inc_ref(v___y_6037_);
                                    crate::leanh::lean_inc(v___y_6036_);
                                    crate::leanh::lean_inc_ref(v___y_6035_);
                                    crate::leanh::lean_inc_ref(v_expr_6065_);
                                    v___x_6066_ = lean_infer_type(
                                        v_expr_6065_,
                                        v___y_6035_,
                                        v___y_6036_,
                                        v___y_6037_,
                                        v___y_6038_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_6066_) == 0 {
                                        v_a_6067_ = crate::leanh::lean_ctor_get(v___x_6066_, 0);
                                        crate::leanh::lean_inc(v_a_6067_);
                                        crate::leanh::lean_dec_ref_known(v___x_6066_, 1);
                                        v___x_6068_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9);
                                        v___x_6069_ = l_Lean_MessageData_ofExpr(v_a_6067_);
                                        v___x_6070_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_6070_, 0, v___x_6068_);
                                        crate::leanh::lean_ctor_set(v___x_6070_, 1, v___x_6069_);
                                        v___x_6071_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_6027_, v___x_6070_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_);
                                        if crate::leanh::lean_obj_tag(v___x_6071_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_6071_, 1);
                                            v___y_5967_ = v_a_6060_;
                                            v___y_5968_ = v___y_6028_;
                                            v___y_5969_ = v___y_6029_;
                                            v___y_5970_ = v___y_6030_;
                                            v___y_5971_ = v___y_6031_;
                                            v___y_5972_ = v___y_6032_;
                                            v___y_5973_ = v___y_6033_;
                                            v___y_5974_ = v___y_6034_;
                                            v___y_5975_ = v___y_6035_;
                                            v___y_5976_ = v___y_6036_;
                                            v___y_5977_ = v___y_6037_;
                                            v___y_5978_ = v___y_6038_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_6060_);
                                            crate::leanh::lean_dec_ref(v_e_5945_);
                                            crate::leanh::lean_dec(v_goal_5944_);
                                            crate::leanh::lean_dec_ref(v_scope_5943_);
                                            v_a_6072_ = crate::leanh::lean_ctor_get(v___x_6071_, 0);
                                            v_isSharedCheck_6079_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_6071_))
                                                    as u8;
                                            if v_isSharedCheck_6079_ == 0 {
                                                v___x_6074_ = v___x_6071_;
                                                v_isShared_6075_ = v_isSharedCheck_6079_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_6072_);
                                                crate::leanh::lean_dec(v___x_6071_);
                                                v___x_6074_ = crate::leanh::lean_box(0);
                                                v_isShared_6075_ = v_isSharedCheck_6079_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_6060_);
                                        crate::leanh::lean_dec(v___y_6027_);
                                        crate::leanh::lean_dec_ref(v_e_5945_);
                                        crate::leanh::lean_dec(v_goal_5944_);
                                        crate::leanh::lean_dec_ref(v_scope_5943_);
                                        v_a_6080_ = crate::leanh::lean_ctor_get(v___x_6066_, 0);
                                        v_isSharedCheck_6087_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6066_)) as u8;
                                        if v_isSharedCheck_6087_ == 0 {
                                            v___x_6082_ = v___x_6066_;
                                            v_isShared_6083_ = v_isSharedCheck_6087_;
                                            state = 15;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6080_);
                                            crate::leanh::lean_dec(v___x_6066_);
                                            v___x_6082_ = crate::leanh::lean_box(0);
                                            v_isShared_6083_ = v_isSharedCheck_6087_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6060_);
                                crate::leanh::lean_dec(v___y_6027_);
                                crate::leanh::lean_dec_ref(v_e_5945_);
                                crate::leanh::lean_dec(v_goal_5944_);
                                crate::leanh::lean_dec_ref(v_scope_5943_);
                                v_a_6088_ = crate::leanh::lean_ctor_get(v___x_6062_, 0);
                                v_isSharedCheck_6095_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6062_)) as u8;
                                if v_isSharedCheck_6095_ == 0 {
                                    v___x_6090_ = v___x_6062_;
                                    v_isShared_6091_ = v_isSharedCheck_6095_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6088_);
                                    crate::leanh::lean_dec(v___x_6062_);
                                    v___x_6090_ = crate::leanh::lean_box(0);
                                    v_isShared_6091_ = v_isSharedCheck_6095_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_6027_);
                            crate::leanh::lean_dec_ref(v_e_5945_);
                            crate::leanh::lean_dec(v_goal_5944_);
                            crate::leanh::lean_dec_ref(v_scope_5943_);
                            v_a_6096_ = crate::leanh::lean_ctor_get(v___x_6059_, 0);
                            v_isSharedCheck_6103_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6059_)) as u8;
                            if v_isSharedCheck_6103_ == 0 {
                                v___x_6098_ = v___x_6059_;
                                v_isShared_6099_ = v_isSharedCheck_6103_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6096_);
                                crate::leanh::lean_dec(v___x_6059_);
                                v___x_6098_ = crate::leanh::lean_box(0);
                                v_isShared_6099_ = v_isSharedCheck_6103_;
                                state = 19;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_6027_);
                    crate::leanh::lean_dec_ref(v___y_6026_);
                    crate::leanh::lean_dec_ref(v_instWP_5950_);
                    crate::leanh::lean_dec_ref(v_ps_5949_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5948_);
                    crate::leanh::lean_dec_ref(v_m_5947_);
                    crate::leanh::lean_dec_ref(v_excessArgs_5946_);
                    crate::leanh::lean_dec_ref(v_e_5945_);
                    crate::leanh::lean_dec(v_goal_5944_);
                    crate::leanh::lean_dec_ref(v_scope_5943_);
                    v_a_6104_ = crate::leanh::lean_ctor_get(v___x_6039_, 0);
                    v_isSharedCheck_6111_ = (!crate::leanh::lean_is_exclusive(v___x_6039_)) as u8;
                    if v_isSharedCheck_6111_ == 0 {
                        v___x_6106_ = v___x_6039_;
                        v_isShared_6107_ = v_isSharedCheck_6111_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6104_);
                        crate::leanh::lean_dec(v___x_6039_);
                        v___x_6106_ = crate::leanh::lean_box(0);
                        v_isShared_6107_ = v_isSharedCheck_6111_;
                        state = 21;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_6054_ == 0 {
                    v___x_6056_ = v___x_6053_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6057_, 0, v_a_6051_);
                    v___x_6056_ = v_reuseFailAlloc_6057_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6056_;
            }
            13 => {
                if v_isShared_6075_ == 0 {
                    v___x_6077_ = v___x_6074_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6078_, 0, v_a_6072_);
                    v___x_6077_ = v_reuseFailAlloc_6078_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6077_;
            }
            15 => {
                if v_isShared_6083_ == 0 {
                    v___x_6085_ = v___x_6082_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6086_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6086_, 0, v_a_6080_);
                    v___x_6085_ = v_reuseFailAlloc_6086_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6085_;
            }
            17 => {
                if v_isShared_6091_ == 0 {
                    v___x_6093_ = v___x_6090_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6094_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6094_, 0, v_a_6088_);
                    v___x_6093_ = v_reuseFailAlloc_6094_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6093_;
            }
            19 => {
                if v_isShared_6099_ == 0 {
                    v___x_6101_ = v___x_6098_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6102_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6102_, 0, v_a_6096_);
                    v___x_6101_ = v_reuseFailAlloc_6102_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6101_;
            }
            21 => {
                if v_isShared_6107_ == 0 {
                    v___x_6109_ = v___x_6106_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
                    v___x_6109_ = v_reuseFailAlloc_6110_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6109_;
            }
            23 => {
                v___x_6129_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6129_, 0, v___y_6115_);
                crate::leanh::lean_ctor_set(v___x_6129_, 1, v___y_6128_);
                crate::leanh::lean_inc(v___y_6125_);
                v___x_6130_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_6125_, v___x_6129_, v___y_6123_, v___y_6118_, v___y_6124_, v___y_6117_);
                if crate::leanh::lean_obj_tag(v___x_6130_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6130_, 1);
                    v___y_6025_ = v___y_6116_;
                    v___y_6026_ = v___y_6122_;
                    v___y_6027_ = v___y_6125_;
                    v___y_6028_ = v___y_6114_;
                    v___y_6029_ = v___y_6121_;
                    v___y_6030_ = v___y_6119_;
                    v___y_6031_ = v___y_6127_;
                    v___y_6032_ = v___y_6120_;
                    v___y_6033_ = v___y_6113_;
                    v___y_6034_ = v___y_6126_;
                    v___y_6035_ = v___y_6123_;
                    v___y_6036_ = v___y_6118_;
                    v___y_6037_ = v___y_6124_;
                    v___y_6038_ = v___y_6117_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6125_);
                    crate::leanh::lean_dec_ref(v___y_6122_);
                    crate::leanh::lean_dec_ref(v_instWP_5950_);
                    crate::leanh::lean_dec_ref(v_ps_5949_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5948_);
                    crate::leanh::lean_dec_ref(v_m_5947_);
                    crate::leanh::lean_dec_ref(v_excessArgs_5946_);
                    crate::leanh::lean_dec_ref(v_e_5945_);
                    crate::leanh::lean_dec(v_goal_5944_);
                    crate::leanh::lean_dec_ref(v_scope_5943_);
                    v_a_6131_ = crate::leanh::lean_ctor_get(v___x_6130_, 0);
                    v_isSharedCheck_6138_ = (!crate::leanh::lean_is_exclusive(v___x_6130_)) as u8;
                    if v_isSharedCheck_6138_ == 0 {
                        v___x_6133_ = v___x_6130_;
                        v_isShared_6134_ = v_isSharedCheck_6138_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6131_);
                        crate::leanh::lean_dec(v___x_6130_);
                        v___x_6133_ = crate::leanh::lean_box(0);
                        v_isShared_6134_ = v_isSharedCheck_6138_;
                        state = 24;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_6134_ == 0 {
                    v___x_6136_ = v___x_6133_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6137_, 0, v_a_6131_);
                    v___x_6136_ = v_reuseFailAlloc_6137_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6136_;
            }
            26 => {
                v_specs_6153_ = crate::leanh::lean_ctor_get(v_scope_5943_, 0);
                crate::leanh::lean_inc_ref(v_e_5945_);
                crate::leanh::lean_inc_ref(v_specs_6153_);
                v___x_6154_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(
                    v_specs_6153_,
                    v_e_5945_,
                    v___y_6147_,
                    v___y_6148_,
                    v___y_6149_,
                    v___y_6150_,
                    v___y_6151_,
                    v___y_6152_,
                );
                if crate::leanh::lean_obj_tag(v___x_6154_) == 0 {
                    v_a_6155_ = crate::leanh::lean_ctor_get(v___x_6154_, 0);
                    v_isSharedCheck_6210_ = (!crate::leanh::lean_is_exclusive(v___x_6154_)) as u8;
                    if v_isSharedCheck_6210_ == 0 {
                        v___x_6157_ = v___x_6154_;
                        v_isShared_6158_ = v_isSharedCheck_6210_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6155_);
                        crate::leanh::lean_dec(v___x_6154_);
                        v___x_6157_ = crate::leanh::lean_box(0);
                        v_isShared_6158_ = v_isSharedCheck_6210_;
                        state = 27;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_6141_);
                    crate::leanh::lean_dec_ref(v_instWP_5950_);
                    crate::leanh::lean_dec_ref(v_ps_5949_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5948_);
                    crate::leanh::lean_dec_ref(v_m_5947_);
                    crate::leanh::lean_dec_ref(v_excessArgs_5946_);
                    crate::leanh::lean_dec_ref(v_e_5945_);
                    crate::leanh::lean_dec(v_goal_5944_);
                    crate::leanh::lean_dec_ref(v_scope_5943_);
                    v_a_6211_ = crate::leanh::lean_ctor_get(v___x_6154_, 0);
                    v_isSharedCheck_6218_ = (!crate::leanh::lean_is_exclusive(v___x_6154_)) as u8;
                    if v_isSharedCheck_6218_ == 0 {
                        v___x_6213_ = v___x_6154_;
                        v_isShared_6214_ = v_isSharedCheck_6218_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6211_);
                        crate::leanh::lean_dec(v___x_6154_);
                        v___x_6213_ = crate::leanh::lean_box(0);
                        v_isShared_6214_ = v_isSharedCheck_6218_;
                        state = 33;
                        continue;
                    }
                }
            }
            27 => {
                if crate::leanh::lean_obj_tag(v_a_6155_) == 0 {
                    crate::leanh::lean_dec(v___y_6141_);
                    crate::leanh::lean_dec_ref(v_instWP_5950_);
                    crate::leanh::lean_dec_ref(v_ps_5949_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5948_);
                    crate::leanh::lean_dec_ref(v_excessArgs_5946_);
                    crate::leanh::lean_dec(v_goal_5944_);
                    v_isSharedCheck_6169_ = (!crate::leanh::lean_is_exclusive(v_scope_5943_)) as u8;
                    if v_isSharedCheck_6169_ == 0 {
                        v_unused_6170_ = crate::leanh::lean_ctor_get(v_scope_5943_, 2);
                        crate::leanh::lean_dec(v_unused_6170_);
                        v_unused_6171_ = crate::leanh::lean_ctor_get(v_scope_5943_, 1);
                        crate::leanh::lean_dec(v_unused_6171_);
                        v_unused_6172_ = crate::leanh::lean_ctor_get(v_scope_5943_, 0);
                        crate::leanh::lean_dec(v_unused_6172_);
                        v___x_6160_ = v_scope_5943_;
                        v_isShared_6161_ = v_isSharedCheck_6169_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_scope_5943_);
                        v___x_6160_ = crate::leanh::lean_box(0);
                        v_isShared_6161_ = v_isSharedCheck_6169_;
                        state = 28;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6157_);
                    v_a_6173_ = crate::leanh::lean_ctor_get(v_a_6155_, 0);
                    crate::leanh::lean_inc(v_a_6173_);
                    crate::leanh::lean_dec_ref_known(v_a_6155_, 1);
                    v_inheritedTraceOptions_6174_ = crate::leanh::lean_ctor_get(v___y_6151_, 13);
                    crate::leanh::lean_inc_ref(v___y_6140_);
                    crate::leanh::lean_inc(v___y_6152_);
                    crate::leanh::lean_inc_ref(v___y_6151_);
                    crate::leanh::lean_inc(v___y_6150_);
                    crate::leanh::lean_inc_ref(v___y_6149_);
                    crate::leanh::lean_inc(v___y_6148_);
                    crate::leanh::lean_inc_ref(v___y_6147_);
                    crate::leanh::lean_inc(v___y_6146_);
                    crate::leanh::lean_inc_ref(v___y_6145_);
                    crate::leanh::lean_inc(v___y_6144_);
                    crate::leanh::lean_inc(v___y_6143_);
                    crate::leanh::lean_inc_ref(v___y_6142_);
                    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_6174_);
                    v___x_6175_ = crate::leanh::lean_apply_13(
                        v___y_6140_,
                        v_inheritedTraceOptions_6174_,
                        v___y_6142_,
                        v___y_6143_,
                        v___y_6144_,
                        v___y_6145_,
                        v___y_6146_,
                        v___y_6147_,
                        v___y_6148_,
                        v___y_6149_,
                        v___y_6150_,
                        v___y_6151_,
                        v___y_6152_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6175_) == 0 {
                        v_a_6176_ = crate::leanh::lean_ctor_get(v___x_6175_, 0);
                        crate::leanh::lean_inc(v_a_6176_);
                        crate::leanh::lean_dec_ref_known(v___x_6175_, 1);
                        v___x_6177_ = (crate::leanh::lean_unbox(v_a_6176_) as u8);
                        crate::leanh::lean_dec(v_a_6176_);
                        if v___x_6177_ == 0 {
                            v___y_6025_ = v___y_6140_;
                            v___y_6026_ = v_a_6173_;
                            v___y_6027_ = v___y_6141_;
                            v___y_6028_ = v___y_6142_;
                            v___y_6029_ = v___y_6143_;
                            v___y_6030_ = v___y_6144_;
                            v___y_6031_ = v___y_6145_;
                            v___y_6032_ = v___y_6146_;
                            v___y_6033_ = v___y_6147_;
                            v___y_6034_ = v___y_6148_;
                            v___y_6035_ = v___y_6149_;
                            v___y_6036_ = v___y_6150_;
                            v___y_6037_ = v___y_6151_;
                            v___y_6038_ = v___y_6152_;
                            state = 10;
                            continue;
                        } else {
                            v_proof_6178_ = crate::leanh::lean_ctor_get(v_a_6173_, 1);
                            v___x_6179_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11);
                            crate::leanh::lean_inc_ref(v_e_5945_);
                            v___x_6180_ = l_Lean_MessageData_ofExpr(v_e_5945_);
                            v___x_6181_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6181_, 0, v___x_6179_);
                            crate::leanh::lean_ctor_set(v___x_6181_, 1, v___x_6180_);
                            v___x_6182_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13);
                            v___x_6183_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6183_, 0, v___x_6181_);
                            crate::leanh::lean_ctor_set(v___x_6183_, 1, v___x_6182_);
                            match crate::leanh::lean_obj_tag(v_proof_6178_) {
                                0 => {
                                    v_declName_6184_ =
                                        crate::leanh::lean_ctor_get(v_proof_6178_, 0);
                                    v___x_6185_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15);
                                    crate::leanh::lean_inc(v_declName_6184_);
                                    v___x_6186_ = l_Lean_MessageData_ofName(v_declName_6184_);
                                    v___x_6187_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6187_, 0, v___x_6185_);
                                    crate::leanh::lean_ctor_set(v___x_6187_, 1, v___x_6186_);
                                    v___y_6113_ = v___y_6147_;
                                    v___y_6114_ = v___y_6142_;
                                    v___y_6115_ = v___x_6183_;
                                    v___y_6116_ = v___y_6140_;
                                    v___y_6117_ = v___y_6152_;
                                    v___y_6118_ = v___y_6150_;
                                    v___y_6119_ = v___y_6144_;
                                    v___y_6120_ = v___y_6146_;
                                    v___y_6121_ = v___y_6143_;
                                    v___y_6122_ = v_a_6173_;
                                    v___y_6123_ = v___y_6149_;
                                    v___y_6124_ = v___y_6151_;
                                    v___y_6125_ = v___y_6141_;
                                    v___y_6126_ = v___y_6148_;
                                    v___y_6127_ = v___y_6145_;
                                    v___y_6128_ = v___x_6187_;
                                    state = 23;
                                    continue;
                                }
                                1 => {
                                    v_fvarId_6188_ = crate::leanh::lean_ctor_get(v_proof_6178_, 0);
                                    v___x_6189_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17);
                                    crate::leanh::lean_inc(v_fvarId_6188_);
                                    v___x_6190_ = l_Lean_mkFVar(v_fvarId_6188_);
                                    v___x_6191_ = l_Lean_MessageData_ofExpr(v___x_6190_);
                                    v___x_6192_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6192_, 0, v___x_6189_);
                                    crate::leanh::lean_ctor_set(v___x_6192_, 1, v___x_6191_);
                                    v___y_6113_ = v___y_6147_;
                                    v___y_6114_ = v___y_6142_;
                                    v___y_6115_ = v___x_6183_;
                                    v___y_6116_ = v___y_6140_;
                                    v___y_6117_ = v___y_6152_;
                                    v___y_6118_ = v___y_6150_;
                                    v___y_6119_ = v___y_6144_;
                                    v___y_6120_ = v___y_6146_;
                                    v___y_6121_ = v___y_6143_;
                                    v___y_6122_ = v_a_6173_;
                                    v___y_6123_ = v___y_6149_;
                                    v___y_6124_ = v___y_6151_;
                                    v___y_6125_ = v___y_6141_;
                                    v___y_6126_ = v___y_6148_;
                                    v___y_6127_ = v___y_6145_;
                                    v___y_6128_ = v___x_6192_;
                                    state = 23;
                                    continue;
                                }
                                _ => {
                                    v_ref_6193_ = crate::leanh::lean_ctor_get(v_proof_6178_, 1);
                                    v_proof_6194_ = crate::leanh::lean_ctor_get(v_proof_6178_, 2);
                                    v___x_6195_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19);
                                    crate::leanh::lean_inc(v_ref_6193_);
                                    v___x_6196_ = l_Lean_MessageData_ofSyntax(v_ref_6193_);
                                    v___x_6197_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6197_, 0, v___x_6195_);
                                    crate::leanh::lean_ctor_set(v___x_6197_, 1, v___x_6196_);
                                    v___x_6198_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21);
                                    v___x_6199_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6199_, 0, v___x_6197_);
                                    crate::leanh::lean_ctor_set(v___x_6199_, 1, v___x_6198_);
                                    crate::leanh::lean_inc_ref(v_proof_6194_);
                                    v___x_6200_ = l_Lean_MessageData_ofExpr(v_proof_6194_);
                                    v___x_6201_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6201_, 0, v___x_6199_);
                                    crate::leanh::lean_ctor_set(v___x_6201_, 1, v___x_6200_);
                                    v___y_6113_ = v___y_6147_;
                                    v___y_6114_ = v___y_6142_;
                                    v___y_6115_ = v___x_6183_;
                                    v___y_6116_ = v___y_6140_;
                                    v___y_6117_ = v___y_6152_;
                                    v___y_6118_ = v___y_6150_;
                                    v___y_6119_ = v___y_6144_;
                                    v___y_6120_ = v___y_6146_;
                                    v___y_6121_ = v___y_6143_;
                                    v___y_6122_ = v_a_6173_;
                                    v___y_6123_ = v___y_6149_;
                                    v___y_6124_ = v___y_6151_;
                                    v___y_6125_ = v___y_6141_;
                                    v___y_6126_ = v___y_6148_;
                                    v___y_6127_ = v___y_6145_;
                                    v___y_6128_ = v___x_6201_;
                                    state = 23;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6173_);
                        crate::leanh::lean_dec(v___y_6141_);
                        crate::leanh::lean_dec_ref(v_instWP_5950_);
                        crate::leanh::lean_dec_ref(v_ps_5949_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_5948_);
                        crate::leanh::lean_dec_ref(v_m_5947_);
                        crate::leanh::lean_dec_ref(v_excessArgs_5946_);
                        crate::leanh::lean_dec_ref(v_e_5945_);
                        crate::leanh::lean_dec(v_goal_5944_);
                        crate::leanh::lean_dec_ref(v_scope_5943_);
                        v_a_6202_ = crate::leanh::lean_ctor_get(v___x_6175_, 0);
                        v_isSharedCheck_6209_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6175_)) as u8;
                        if v_isSharedCheck_6209_ == 0 {
                            v___x_6204_ = v___x_6175_;
                            v_isShared_6205_ = v_isSharedCheck_6209_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6202_);
                            crate::leanh::lean_dec(v___x_6175_);
                            v___x_6204_ = crate::leanh::lean_box(0);
                            v_isShared_6205_ = v_isSharedCheck_6209_;
                            state = 31;
                            continue;
                        }
                    }
                }
            }
            28 => {
                v_a_6162_ = crate::leanh::lean_ctor_get(v_a_6155_, 0);
                crate::leanh::lean_inc(v_a_6162_);
                crate::leanh::lean_dec_ref_known(v_a_6155_, 1);
                if v_isShared_6161_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6160_, 3);
                    crate::leanh::lean_ctor_set(v___x_6160_, 2, v_a_6162_);
                    crate::leanh::lean_ctor_set(v___x_6160_, 1, v_m_5947_);
                    crate::leanh::lean_ctor_set(v___x_6160_, 0, v_e_5945_);
                    v___x_6164_ = v___x_6160_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6168_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6168_, 0, v_e_5945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6168_, 1, v_m_5947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6168_, 2, v_a_6162_);
                    v___x_6164_ = v_reuseFailAlloc_6168_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_6158_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6157_, 0, v___x_6164_);
                    v___x_6166_ = v___x_6157_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6167_, 0, v___x_6164_);
                    v___x_6166_ = v_reuseFailAlloc_6167_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_6166_;
            }
            31 => {
                if v_isShared_6205_ == 0 {
                    v___x_6207_ = v___x_6204_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6208_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6208_, 0, v_a_6202_);
                    v___x_6207_ = v_reuseFailAlloc_6208_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_6207_;
            }
            33 => {
                if v_isShared_6214_ == 0 {
                    v___x_6216_ = v___x_6213_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6217_, 0, v_a_6211_);
                    v___x_6216_ = v_reuseFailAlloc_6217_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6216_;
            }
            35 => {
                if v___y_6220_ == 0 {
                    crate::leanh::lean_dec_ref(v_instWP_5950_);
                    crate::leanh::lean_dec_ref(v_ps_5949_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5948_);
                    crate::leanh::lean_dec_ref(v_m_5947_);
                    crate::leanh::lean_dec_ref(v_excessArgs_5946_);
                    crate::leanh::lean_dec(v_goal_5944_);
                    crate::leanh::lean_dec_ref(v_scope_5943_);
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_6221_ = crate::leanh::lean_ctor_get(v_a_5960_, 13);
                    v_cls_6222_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                    v___f_6223_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22;
                    v___x_6224_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(v_cls_6222_, v_inheritedTraceOptions_6221_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_, v_a_5961_);
                    v_a_6225_ = crate::leanh::lean_ctor_get(v___x_6224_, 0);
                    crate::leanh::lean_inc(v_a_6225_);
                    crate::leanh::lean_dec_ref(v___x_6224_);
                    v___x_6226_ = (crate::leanh::lean_unbox(v_a_6225_) as u8);
                    crate::leanh::lean_dec(v_a_6225_);
                    if v___x_6226_ == 0 {
                        v___y_6140_ = v___f_6223_;
                        v___y_6141_ = v_cls_6222_;
                        v___y_6142_ = v_a_5951_;
                        v___y_6143_ = v_a_5952_;
                        v___y_6144_ = v_a_5953_;
                        v___y_6145_ = v_a_5954_;
                        v___y_6146_ = v_a_5955_;
                        v___y_6147_ = v_a_5956_;
                        v___y_6148_ = v_a_5957_;
                        v___y_6149_ = v_a_5958_;
                        v___y_6150_ = v_a_5959_;
                        v___y_6151_ = v_a_5960_;
                        v___y_6152_ = v_a_5961_;
                        state = 26;
                        continue;
                    } else {
                        v___x_6227_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24);
                        crate::leanh::lean_inc_ref(v_e_5945_);
                        v___x_6228_ = l_Lean_MessageData_ofExpr(v_e_5945_);
                        v___x_6229_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6229_, 0, v___x_6227_);
                        crate::leanh::lean_ctor_set(v___x_6229_, 1, v___x_6228_);
                        v___x_6230_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26);
                        v___x_6231_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6231_, 0, v___x_6229_);
                        crate::leanh::lean_ctor_set(v___x_6231_, 1, v___x_6230_);
                        crate::leanh::lean_inc_ref(v_excessArgs_5946_);
                        v___x_6232_ = lean_array_to_list(v_excessArgs_5946_);
                        v___x_6233_ = crate::leanh::lean_box(0);
                        v___x_6234_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_6232_, v___x_6233_);
                        v___x_6235_ = l_Lean_MessageData_ofList(v___x_6234_);
                        v___x_6236_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6236_, 0, v___x_6231_);
                        crate::leanh::lean_ctor_set(v___x_6236_, 1, v___x_6235_);
                        v___x_6237_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_6222_, v___x_6236_, v_a_5958_, v_a_5959_, v_a_5960_, v_a_5961_);
                        if crate::leanh::lean_obj_tag(v___x_6237_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6237_, 1);
                            v___y_6140_ = v___f_6223_;
                            v___y_6141_ = v_cls_6222_;
                            v___y_6142_ = v_a_5951_;
                            v___y_6143_ = v_a_5952_;
                            v___y_6144_ = v_a_5953_;
                            v___y_6145_ = v_a_5954_;
                            v___y_6146_ = v_a_5955_;
                            v___y_6147_ = v_a_5956_;
                            v___y_6148_ = v_a_5957_;
                            v___y_6149_ = v_a_5958_;
                            v___y_6150_ = v_a_5959_;
                            v___y_6151_ = v_a_5960_;
                            v___y_6152_ = v_a_5961_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_instWP_5950_);
                            crate::leanh::lean_dec_ref(v_ps_5949_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_5948_);
                            crate::leanh::lean_dec_ref(v_m_5947_);
                            crate::leanh::lean_dec_ref(v_excessArgs_5946_);
                            crate::leanh::lean_dec_ref(v_e_5945_);
                            crate::leanh::lean_dec(v_goal_5944_);
                            crate::leanh::lean_dec_ref(v_scope_5943_);
                            v_a_6238_ = crate::leanh::lean_ctor_get(v___x_6237_, 0);
                            v_isSharedCheck_6245_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6237_)) as u8;
                            if v_isSharedCheck_6245_ == 0 {
                                v___x_6240_ = v___x_6237_;
                                v_isShared_6241_ = v_isSharedCheck_6245_;
                                state = 36;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6238_);
                                crate::leanh::lean_dec(v___x_6237_);
                                v___x_6240_ = crate::leanh::lean_box(0);
                                v_isShared_6241_ = v_isSharedCheck_6245_;
                                state = 36;
                                continue;
                            }
                        }
                    }
                }
            }
            36 => {
                if v_isShared_6241_ == 0 {
                    v___x_6243_ = v___x_6240_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_6244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6244_, 0, v_a_6238_);
                    v___x_6243_ = v_reuseFailAlloc_6244_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_6243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_scope_6249_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_goal_6250_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_e_6251_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_excessArgs_6252_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_m_6253_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_00_u03c3s_6254_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_ps_6255_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_instWP_6256_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_6257_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_6258_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_6259_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_6260_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_6261_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_6262_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_6263_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_6264_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_6265_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_6266_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_6267_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_a_6268_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_res_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6269_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_scope_6249_, v_goal_6250_, v_e_6251_, v_excessArgs_6252_, v_m_6253_, v_00_u03c3s_6254_, v_ps_6255_, v_instWP_6256_, v_a_6257_, v_a_6258_, v_a_6259_, v_a_6260_, v_a_6261_, v_a_6262_, v_a_6263_, v_a_6264_, v_a_6265_, v_a_6266_, v_a_6267_);
    crate::leanh::lean_dec(v_a_6267_);
    crate::leanh::lean_dec_ref(v_a_6266_);
    crate::leanh::lean_dec(v_a_6265_);
    crate::leanh::lean_dec_ref(v_a_6264_);
    crate::leanh::lean_dec(v_a_6263_);
    crate::leanh::lean_dec_ref(v_a_6262_);
    crate::leanh::lean_dec(v_a_6261_);
    crate::leanh::lean_dec_ref(v_a_6260_);
    crate::leanh::lean_dec(v_a_6259_);
    crate::leanh::lean_dec(v_a_6258_);
    crate::leanh::lean_dec_ref(v_a_6257_);
    return v_res_6269_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0(
    mut v_x_6270_: *mut crate::leanh::LeanObject,
    mut v___y_6271_: *mut crate::leanh::LeanObject,
    mut v___y_6272_: *mut crate::leanh::LeanObject,
    mut v___y_6273_: *mut crate::leanh::LeanObject,
    mut v___y_6274_: *mut crate::leanh::LeanObject,
    mut v___y_6275_: *mut crate::leanh::LeanObject,
    mut v___y_6276_: *mut crate::leanh::LeanObject,
    mut v___y_6277_: *mut crate::leanh::LeanObject,
    mut v___y_6278_: *mut crate::leanh::LeanObject,
    mut v___y_6279_: *mut crate::leanh::LeanObject,
    mut v___y_6280_: *mut crate::leanh::LeanObject,
    mut v___y_6281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_6277_);
    crate::leanh::lean_inc_ref(v___y_6276_);
    crate::leanh::lean_inc(v___y_6275_);
    crate::leanh::lean_inc_ref(v___y_6274_);
    crate::leanh::lean_inc(v___y_6273_);
    crate::leanh::lean_inc(v___y_6272_);
    crate::leanh::lean_inc_ref(v___y_6271_);
    v___x_6283_ = crate::leanh::lean_apply_12(
        v_x_6270_,
        v___y_6271_,
        v___y_6272_,
        v___y_6273_,
        v___y_6274_,
        v___y_6275_,
        v___y_6276_,
        v___y_6277_,
        v___y_6278_,
        v___y_6279_,
        v___y_6280_,
        v___y_6281_,
        crate::leanh::lean_box(0),
    );
    return v___x_6283_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0___boxed(
    mut v_x_6284_: *mut crate::leanh::LeanObject,
    mut v___y_6285_: *mut crate::leanh::LeanObject,
    mut v___y_6286_: *mut crate::leanh::LeanObject,
    mut v___y_6287_: *mut crate::leanh::LeanObject,
    mut v___y_6288_: *mut crate::leanh::LeanObject,
    mut v___y_6289_: *mut crate::leanh::LeanObject,
    mut v___y_6290_: *mut crate::leanh::LeanObject,
    mut v___y_6291_: *mut crate::leanh::LeanObject,
    mut v___y_6292_: *mut crate::leanh::LeanObject,
    mut v___y_6293_: *mut crate::leanh::LeanObject,
    mut v___y_6294_: *mut crate::leanh::LeanObject,
    mut v___y_6295_: *mut crate::leanh::LeanObject,
    mut v___y_6296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6297_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0(v_x_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_, v___y_6294_, v___y_6295_);
    crate::leanh::lean_dec(v___y_6291_);
    crate::leanh::lean_dec_ref(v___y_6290_);
    crate::leanh::lean_dec(v___y_6289_);
    crate::leanh::lean_dec_ref(v___y_6288_);
    crate::leanh::lean_dec(v___y_6287_);
    crate::leanh::lean_dec(v___y_6286_);
    crate::leanh::lean_dec_ref(v___y_6285_);
    return v_res_6297_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(
    mut v_mvarId_6298_: *mut crate::leanh::LeanObject,
    mut v_x_6299_: *mut crate::leanh::LeanObject,
    mut v___y_6300_: *mut crate::leanh::LeanObject,
    mut v___y_6301_: *mut crate::leanh::LeanObject,
    mut v___y_6302_: *mut crate::leanh::LeanObject,
    mut v___y_6303_: *mut crate::leanh::LeanObject,
    mut v___y_6304_: *mut crate::leanh::LeanObject,
    mut v___y_6305_: *mut crate::leanh::LeanObject,
    mut v___y_6306_: *mut crate::leanh::LeanObject,
    mut v___y_6307_: *mut crate::leanh::LeanObject,
    mut v___y_6308_: *mut crate::leanh::LeanObject,
    mut v___y_6309_: *mut crate::leanh::LeanObject,
    mut v___y_6310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6317_: u8 = 0;
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_6306_);
                crate::leanh::lean_inc_ref(v___y_6305_);
                crate::leanh::lean_inc(v___y_6304_);
                crate::leanh::lean_inc_ref(v___y_6303_);
                crate::leanh::lean_inc(v___y_6302_);
                crate::leanh::lean_inc(v___y_6301_);
                crate::leanh::lean_inc_ref(v___y_6300_);
                v___f_6312_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                crate::leanh::lean_closure_set(v___f_6312_, 0, v_x_6299_);
                crate::leanh::lean_closure_set(v___f_6312_, 1, v___y_6300_);
                crate::leanh::lean_closure_set(v___f_6312_, 2, v___y_6301_);
                crate::leanh::lean_closure_set(v___f_6312_, 3, v___y_6302_);
                crate::leanh::lean_closure_set(v___f_6312_, 4, v___y_6303_);
                crate::leanh::lean_closure_set(v___f_6312_, 5, v___y_6304_);
                crate::leanh::lean_closure_set(v___f_6312_, 6, v___y_6305_);
                crate::leanh::lean_closure_set(v___f_6312_, 7, v___y_6306_);
                v___x_6313_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_6298_,
                    v___f_6312_,
                    v___y_6307_,
                    v___y_6308_,
                    v___y_6309_,
                    v___y_6310_,
                );
                if crate::leanh::lean_obj_tag(v___x_6313_) == 0 {
                    return v___x_6313_;
                } else {
                    v_a_6314_ = crate::leanh::lean_ctor_get(v___x_6313_, 0);
                    v_isSharedCheck_6321_ = (!crate::leanh::lean_is_exclusive(v___x_6313_)) as u8;
                    if v_isSharedCheck_6321_ == 0 {
                        v___x_6316_ = v___x_6313_;
                        v_isShared_6317_ = v_isSharedCheck_6321_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6314_);
                        crate::leanh::lean_dec(v___x_6313_);
                        v___x_6316_ = crate::leanh::lean_box(0);
                        v_isShared_6317_ = v_isSharedCheck_6321_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6317_ == 0 {
                    v___x_6319_ = v___x_6316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6320_, 0, v_a_6314_);
                    v___x_6319_ = v_reuseFailAlloc_6320_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___boxed(
    mut v_mvarId_6322_: *mut crate::leanh::LeanObject,
    mut v_x_6323_: *mut crate::leanh::LeanObject,
    mut v___y_6324_: *mut crate::leanh::LeanObject,
    mut v___y_6325_: *mut crate::leanh::LeanObject,
    mut v___y_6326_: *mut crate::leanh::LeanObject,
    mut v___y_6327_: *mut crate::leanh::LeanObject,
    mut v___y_6328_: *mut crate::leanh::LeanObject,
    mut v___y_6329_: *mut crate::leanh::LeanObject,
    mut v___y_6330_: *mut crate::leanh::LeanObject,
    mut v___y_6331_: *mut crate::leanh::LeanObject,
    mut v___y_6332_: *mut crate::leanh::LeanObject,
    mut v___y_6333_: *mut crate::leanh::LeanObject,
    mut v___y_6334_: *mut crate::leanh::LeanObject,
    mut v___y_6335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6336_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_mvarId_6322_, v_x_6323_, v___y_6324_, v___y_6325_, v___y_6326_, v___y_6327_, v___y_6328_, v___y_6329_, v___y_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
    crate::leanh::lean_dec(v___y_6334_);
    crate::leanh::lean_dec_ref(v___y_6333_);
    crate::leanh::lean_dec(v___y_6332_);
    crate::leanh::lean_dec_ref(v___y_6331_);
    crate::leanh::lean_dec(v___y_6330_);
    crate::leanh::lean_dec_ref(v___y_6329_);
    crate::leanh::lean_dec(v___y_6328_);
    crate::leanh::lean_dec_ref(v___y_6327_);
    crate::leanh::lean_dec(v___y_6326_);
    crate::leanh::lean_dec(v___y_6325_);
    crate::leanh::lean_dec_ref(v___y_6324_);
    return v_res_6336_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1(
    mut v_00_u03b1_6337_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6338_: *mut crate::leanh::LeanObject,
    mut v_x_6339_: *mut crate::leanh::LeanObject,
    mut v___y_6340_: *mut crate::leanh::LeanObject,
    mut v___y_6341_: *mut crate::leanh::LeanObject,
    mut v___y_6342_: *mut crate::leanh::LeanObject,
    mut v___y_6343_: *mut crate::leanh::LeanObject,
    mut v___y_6344_: *mut crate::leanh::LeanObject,
    mut v___y_6345_: *mut crate::leanh::LeanObject,
    mut v___y_6346_: *mut crate::leanh::LeanObject,
    mut v___y_6347_: *mut crate::leanh::LeanObject,
    mut v___y_6348_: *mut crate::leanh::LeanObject,
    mut v___y_6349_: *mut crate::leanh::LeanObject,
    mut v___y_6350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6352_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_mvarId_6338_, v_x_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_, v___y_6349_, v___y_6350_);
    return v___x_6352_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___boxed(
    mut v_00_u03b1_6353_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6354_: *mut crate::leanh::LeanObject,
    mut v_x_6355_: *mut crate::leanh::LeanObject,
    mut v___y_6356_: *mut crate::leanh::LeanObject,
    mut v___y_6357_: *mut crate::leanh::LeanObject,
    mut v___y_6358_: *mut crate::leanh::LeanObject,
    mut v___y_6359_: *mut crate::leanh::LeanObject,
    mut v___y_6360_: *mut crate::leanh::LeanObject,
    mut v___y_6361_: *mut crate::leanh::LeanObject,
    mut v___y_6362_: *mut crate::leanh::LeanObject,
    mut v___y_6363_: *mut crate::leanh::LeanObject,
    mut v___y_6364_: *mut crate::leanh::LeanObject,
    mut v___y_6365_: *mut crate::leanh::LeanObject,
    mut v___y_6366_: *mut crate::leanh::LeanObject,
    mut v___y_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6368_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1(
            v_00_u03b1_6353_,
            v_mvarId_6354_,
            v_x_6355_,
            v___y_6356_,
            v___y_6357_,
            v___y_6358_,
            v___y_6359_,
            v___y_6360_,
            v___y_6361_,
            v___y_6362_,
            v___y_6363_,
            v___y_6364_,
            v___y_6365_,
            v___y_6366_,
        );
    crate::leanh::lean_dec(v___y_6366_);
    crate::leanh::lean_dec_ref(v___y_6365_);
    crate::leanh::lean_dec(v___y_6364_);
    crate::leanh::lean_dec_ref(v___y_6363_);
    crate::leanh::lean_dec(v___y_6362_);
    crate::leanh::lean_dec_ref(v___y_6361_);
    crate::leanh::lean_dec(v___y_6360_);
    crate::leanh::lean_dec_ref(v___y_6359_);
    crate::leanh::lean_dec(v___y_6358_);
    crate::leanh::lean_dec(v___y_6357_);
    crate::leanh::lean_dec_ref(v___y_6356_);
    return v_res_6368_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__0(
    mut v_x_6369_: *mut crate::leanh::LeanObject,
    mut v_x_6370_: *mut crate::leanh::LeanObject,
    mut v_x_6371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6369_) == 5 {
                    v_fn_6372_ = crate::leanh::lean_ctor_get(v_x_6369_, 0);
                    crate::leanh::lean_inc_ref(v_fn_6372_);
                    v_arg_6373_ = crate::leanh::lean_ctor_get(v_x_6369_, 1);
                    crate::leanh::lean_inc_ref(v_arg_6373_);
                    crate::leanh::lean_dec_ref_known(v_x_6369_, 2);
                    v___x_6374_ = lean_array_set(v_x_6370_, v_x_6371_, v_arg_6373_);
                    v___x_6375_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6376_ = lean_nat_sub(v_x_6371_, v___x_6375_);
                    crate::leanh::lean_dec(v_x_6371_);
                    v_x_6369_ = v_fn_6372_;
                    v_x_6370_ = v___x_6374_;
                    v_x_6371_ = v___x_6376_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_6371_);
                    v___x_6378_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6378_, 0, v_x_6369_);
                    crate::leanh::lean_ctor_set(v___x_6378_, 1, v_x_6370_);
                    return v___x_6378_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6384_ = crate::leanh::lean_box(0);
    v_dummy_6385_ = l_Lean_Expr_sort___override(v___x_6384_);
    return v_dummy_6385_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6401_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8;
    v___x_6402_ = l_Lean_stringToMessageData(v___x_6401_);
    return v___x_6402_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6404_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10;
    v___x_6405_ = l_Lean_stringToMessageData(v___x_6404_);
    return v___x_6405_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(
    mut v_goal_6406_: *mut crate::leanh::LeanObject,
    mut v_scope_6407_: *mut crate::leanh::LeanObject,
    mut v___y_6408_: *mut crate::leanh::LeanObject,
    mut v___y_6409_: *mut crate::leanh::LeanObject,
    mut v___y_6410_: *mut crate::leanh::LeanObject,
    mut v___y_6411_: *mut crate::leanh::LeanObject,
    mut v___y_6412_: *mut crate::leanh::LeanObject,
    mut v___y_6413_: *mut crate::leanh::LeanObject,
    mut v___y_6414_: *mut crate::leanh::LeanObject,
    mut v___y_6415_: *mut crate::leanh::LeanObject,
    mut v___y_6416_: *mut crate::leanh::LeanObject,
    mut v___y_6417_: *mut crate::leanh::LeanObject,
    mut v___y_6418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gs_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6441_: u8 = 0;
    let mut v___x_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6448_: u8 = 0;
    let mut v_unused_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6453_: u8 = 0;
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6457_: u8 = 0;
    let mut v___y_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6489_: u8 = 0;
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6496_: u8 = 0;
    let mut v_unused_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6501_: u8 = 0;
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6514_: u8 = 0;
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6519_: u8 = 0;
    let mut v_unused_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6524_: u8 = 0;
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6540_: u8 = 0;
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6544_: u8 = 0;
    let mut v_a_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6548_: u8 = 0;
    let mut v___x_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6552_: u8 = 0;
    let mut v_a_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6556_: u8 = 0;
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6560_: u8 = 0;
    let mut v_a_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6564_: u8 = 0;
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6568_: u8 = 0;
    let mut v_a_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6572_: u8 = 0;
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6576_: u8 = 0;
    let mut v_a_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6580_: u8 = 0;
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6584_: u8 = 0;
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6589_: u8 = 0;
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6597_: u8 = 0;
    let mut v_cls_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6624_: u8 = 0;
    let mut v_arg_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: u8 = 0;
    let mut v_arg_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: u8 = 0;
    let mut v_arg_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: u8 = 0;
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: u8 = 0;
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6658_: u8 = 0;
    let mut v_val_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6664_: u8 = 0;
    let mut v_a_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6668_: u8 = 0;
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6672_: u8 = 0;
    let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: u8 = 0;
    let mut v_arg_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: u8 = 0;
    let mut v_arg_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: u8 = 0;
    let mut v_arg_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: u8 = 0;
    let mut v_arg_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: u8 = 0;
    let mut v_arg_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: u8 = 0;
    let mut v_options_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6696_: u8 = 0;
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: u8 = 0;
    let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6711_: u8 = 0;
    let mut v___x_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6715_: u8 = 0;
    let mut v_reuseFailAlloc_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6717_: u8 = 0;
    let mut v_a_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6721_: u8 = 0;
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6725_: u8 = 0;
    let mut v_a_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6729_: u8 = 0;
    let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6733_: u8 = 0;
    let mut v_a_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6737_: u8 = 0;
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6741_: u8 = 0;
    let mut v_a_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6745_: u8 = 0;
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6749_: u8 = 0;
    let mut v_a_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6753_: u8 = 0;
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6757_: u8 = 0;
    let mut v_a_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6761_: u8 = 0;
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6765_: u8 = 0;
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: u8 = 0;
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6775_: u8 = 0;
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6779_: u8 = 0;
    let mut v_isSharedCheck_6780_: u8 = 0;
    let mut v_a_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6784_: u8 = 0;
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_goal_6406_);
                v___x_6585_ = l_Lean_MVarId_getType(
                    v_goal_6406_,
                    v___y_6415_,
                    v___y_6416_,
                    v___y_6417_,
                    v___y_6418_,
                );
                if crate::leanh::lean_obj_tag(v___x_6585_) == 0 {
                    v_a_6586_ = crate::leanh::lean_ctor_get(v___x_6585_, 0);
                    v_isSharedCheck_6780_ = (!crate::leanh::lean_is_exclusive(v___x_6585_)) as u8;
                    if v_isSharedCheck_6780_ == 0 {
                        v___x_6588_ = v___x_6585_;
                        v_isShared_6589_ = v_isSharedCheck_6780_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6586_);
                        crate::leanh::lean_dec(v___x_6585_);
                        v___x_6588_ = crate::leanh::lean_box(0);
                        v_isShared_6589_ = v_isSharedCheck_6780_;
                        state = 30;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_scope_6407_);
                    crate::leanh::lean_dec(v_goal_6406_);
                    v_a_6781_ = crate::leanh::lean_ctor_get(v___x_6585_, 0);
                    v_isSharedCheck_6788_ = (!crate::leanh::lean_is_exclusive(v___x_6585_)) as u8;
                    if v_isSharedCheck_6788_ == 0 {
                        v___x_6783_ = v___x_6585_;
                        v_isShared_6784_ = v_isSharedCheck_6788_;
                        state = 56;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6781_);
                        crate::leanh::lean_dec(v___x_6585_);
                        v___x_6783_ = crate::leanh::lean_box(0);
                        v_isShared_6784_ = v_isSharedCheck_6788_;
                        state = 56;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6422_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6422_, 0, v_scope_6407_);
                crate::leanh::lean_ctor_set(v___x_6422_, 1, v_gs_6421_);
                v___x_6423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6423_, 0, v___x_6422_);
                return v___x_6423_;
            }
            2 => {
                v___x_6426_ = crate::leanh::lean_box(0);
                v___x_6427_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6427_, 0, v_g_6425_);
                crate::leanh::lean_ctor_set(v___x_6427_, 1, v___x_6426_);
                v___x_6428_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6428_, 0, v_scope_6407_);
                crate::leanh::lean_ctor_set(v___x_6428_, 1, v___x_6427_);
                v___x_6429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6429_, 0, v___x_6428_);
                return v___x_6429_;
            }
            3 => {
                v___x_6432_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6432_, 0, v___y_6431_);
                v___x_6433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6433_, 0, v___x_6432_);
                return v___x_6433_;
            }
            4 => {
                v___x_6438_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_6437_);
                if crate::leanh::lean_obj_tag(v___x_6438_) == 0 {
                    v_isSharedCheck_6448_ = (!crate::leanh::lean_is_exclusive(v___x_6438_)) as u8;
                    if v_isSharedCheck_6448_ == 0 {
                        v_unused_6449_ = crate::leanh::lean_ctor_get(v___x_6438_, 0);
                        crate::leanh::lean_dec(v_unused_6449_);
                        v___x_6440_ = v___x_6438_;
                        v_isShared_6441_ = v_isSharedCheck_6448_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6438_);
                        v___x_6440_ = crate::leanh::lean_box(0);
                        v_isShared_6441_ = v_isSharedCheck_6448_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_g_6436_);
                    crate::leanh::lean_dec_ref(v___y_6435_);
                    v_a_6450_ = crate::leanh::lean_ctor_get(v___x_6438_, 0);
                    v_isSharedCheck_6457_ = (!crate::leanh::lean_is_exclusive(v___x_6438_)) as u8;
                    if v_isSharedCheck_6457_ == 0 {
                        v___x_6452_ = v___x_6438_;
                        v_isShared_6453_ = v_isSharedCheck_6457_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6450_);
                        crate::leanh::lean_dec(v___x_6438_);
                        v___x_6452_ = crate::leanh::lean_box(0);
                        v_isShared_6453_ = v_isSharedCheck_6457_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_6442_ = crate::leanh::lean_box(0);
                v___x_6443_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6443_, 0, v_g_6436_);
                crate::leanh::lean_ctor_set(v___x_6443_, 1, v___x_6442_);
                v___x_6444_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6444_, 0, v___y_6435_);
                crate::leanh::lean_ctor_set(v___x_6444_, 1, v___x_6443_);
                if v_isShared_6441_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6440_, 0, v___x_6444_);
                    v___x_6446_ = v___x_6440_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6447_, 0, v___x_6444_);
                    v___x_6446_ = v_reuseFailAlloc_6447_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6446_;
            }
            7 => {
                if v_isShared_6453_ == 0 {
                    v___x_6455_ = v___x_6452_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6456_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_a_6450_);
                    v___x_6455_ = v_reuseFailAlloc_6456_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6455_;
            }
            9 => {
                crate::leanh::lean_inc_ref(v___y_6461_);
                crate::leanh::lean_inc_ref(v___y_6459_);
                crate::leanh::lean_inc_ref(v___y_6470_);
                crate::leanh::lean_inc_ref(v___y_6464_);
                crate::leanh::lean_inc_ref(v___y_6462_);
                crate::leanh::lean_inc_ref(v___y_6465_);
                crate::leanh::lean_inc_ref(v___y_6467_);
                crate::leanh::lean_inc_ref(v___y_6463_);
                crate::leanh::lean_inc_ref(v___y_6466_);
                crate::leanh::lean_inc_ref(v___y_6460_);
                crate::leanh::lean_inc_ref(v___y_6469_);
                crate::leanh::lean_inc_ref(v___y_6468_);
                crate::leanh::lean_inc(v_goal_6406_);
                v___x_6483_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(v_goal_6406_, v___y_6468_, v___y_6469_, v___y_6460_, v___y_6466_, v___y_6463_, v___y_6467_, v___y_6465_, v___y_6462_, v___y_6464_, v___y_6470_, v___y_6459_, v___y_6461_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                if crate::leanh::lean_obj_tag(v___x_6483_) == 0 {
                    v_a_6484_ = crate::leanh::lean_ctor_get(v___x_6483_, 0);
                    crate::leanh::lean_inc(v_a_6484_);
                    crate::leanh::lean_dec_ref_known(v___x_6483_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6484_) == 1 {
                        crate::leanh::lean_dec_ref(v___y_6471_);
                        crate::leanh::lean_dec_ref(v___y_6470_);
                        crate::leanh::lean_dec_ref(v___y_6469_);
                        crate::leanh::lean_dec_ref(v___y_6468_);
                        crate::leanh::lean_dec_ref(v___y_6467_);
                        crate::leanh::lean_dec_ref(v___y_6466_);
                        crate::leanh::lean_dec_ref(v___y_6465_);
                        crate::leanh::lean_dec_ref(v___y_6464_);
                        crate::leanh::lean_dec_ref(v___y_6463_);
                        crate::leanh::lean_dec_ref(v___y_6462_);
                        crate::leanh::lean_dec_ref(v___y_6461_);
                        crate::leanh::lean_dec_ref(v___y_6460_);
                        crate::leanh::lean_dec_ref(v___y_6459_);
                        crate::leanh::lean_dec(v_goal_6406_);
                        v_val_6485_ = crate::leanh::lean_ctor_get(v_a_6484_, 0);
                        crate::leanh::lean_inc(v_val_6485_);
                        crate::leanh::lean_dec_ref_known(v_a_6484_, 1);
                        v___x_6486_ =
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_6473_);
                        if crate::leanh::lean_obj_tag(v___x_6486_) == 0 {
                            v_isSharedCheck_6496_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6486_)) as u8;
                            if v_isSharedCheck_6496_ == 0 {
                                v_unused_6497_ = crate::leanh::lean_ctor_get(v___x_6486_, 0);
                                crate::leanh::lean_dec(v_unused_6497_);
                                v___x_6488_ = v___x_6486_;
                                v_isShared_6489_ = v_isSharedCheck_6496_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6486_);
                                v___x_6488_ = crate::leanh::lean_box(0);
                                v_isShared_6489_ = v_isSharedCheck_6496_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_6485_);
                            crate::leanh::lean_dec_ref(v_scope_6407_);
                            v_a_6498_ = crate::leanh::lean_ctor_get(v___x_6486_, 0);
                            v_isSharedCheck_6505_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6486_)) as u8;
                            if v_isSharedCheck_6505_ == 0 {
                                v___x_6500_ = v___x_6486_;
                                v_isShared_6501_ = v_isSharedCheck_6505_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6498_);
                                crate::leanh::lean_dec(v___x_6486_);
                                v___x_6500_ = crate::leanh::lean_box(0);
                                v_isShared_6501_ = v_isSharedCheck_6505_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6484_);
                        crate::leanh::lean_inc(v_goal_6406_);
                        v___x_6506_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(
                            v_scope_6407_,
                            v_goal_6406_,
                            v___y_6472_,
                            v___y_6473_,
                            v___y_6474_,
                            v___y_6475_,
                            v___y_6476_,
                            v___y_6477_,
                            v___y_6478_,
                            v___y_6479_,
                            v___y_6480_,
                            v___y_6481_,
                            v___y_6482_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6506_) == 0 {
                            v_a_6507_ = crate::leanh::lean_ctor_get(v___x_6506_, 0);
                            crate::leanh::lean_inc(v_a_6507_);
                            crate::leanh::lean_dec_ref_known(v___x_6506_, 1);
                            crate::leanh::lean_inc_ref(v___y_6471_);
                            crate::leanh::lean_inc_ref(v___y_6459_);
                            crate::leanh::lean_inc_ref(v___y_6470_);
                            crate::leanh::lean_inc_ref(v___y_6464_);
                            crate::leanh::lean_inc_ref(v___y_6462_);
                            crate::leanh::lean_inc_ref(v___y_6465_);
                            crate::leanh::lean_inc_ref(v___y_6467_);
                            crate::leanh::lean_inc_ref(v___y_6463_);
                            crate::leanh::lean_inc_ref(v___y_6466_);
                            crate::leanh::lean_inc_ref(v___y_6460_);
                            crate::leanh::lean_inc_ref(v___y_6469_);
                            crate::leanh::lean_inc_ref(v___y_6468_);
                            crate::leanh::lean_inc(v_goal_6406_);
                            v___x_6508_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(v_goal_6406_, v___y_6468_, v___y_6469_, v___y_6460_, v___y_6466_, v___y_6463_, v___y_6467_, v___y_6465_, v___y_6462_, v___y_6464_, v___y_6470_, v___y_6459_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                            if crate::leanh::lean_obj_tag(v___x_6508_) == 0 {
                                v_a_6509_ = crate::leanh::lean_ctor_get(v___x_6508_, 0);
                                crate::leanh::lean_inc(v_a_6509_);
                                crate::leanh::lean_dec_ref_known(v___x_6508_, 1);
                                if crate::leanh::lean_obj_tag(v_a_6509_) == 1 {
                                    crate::leanh::lean_dec_ref(v___y_6471_);
                                    crate::leanh::lean_dec_ref(v___y_6470_);
                                    crate::leanh::lean_dec_ref(v___y_6469_);
                                    crate::leanh::lean_dec_ref(v___y_6468_);
                                    crate::leanh::lean_dec_ref(v___y_6467_);
                                    crate::leanh::lean_dec_ref(v___y_6466_);
                                    crate::leanh::lean_dec_ref(v___y_6465_);
                                    crate::leanh::lean_dec_ref(v___y_6464_);
                                    crate::leanh::lean_dec_ref(v___y_6463_);
                                    crate::leanh::lean_dec_ref(v___y_6462_);
                                    crate::leanh::lean_dec_ref(v___y_6461_);
                                    crate::leanh::lean_dec_ref(v___y_6460_);
                                    crate::leanh::lean_dec_ref(v___y_6459_);
                                    crate::leanh::lean_dec(v_goal_6406_);
                                    v_val_6510_ = crate::leanh::lean_ctor_get(v_a_6509_, 0);
                                    crate::leanh::lean_inc(v_val_6510_);
                                    crate::leanh::lean_dec_ref_known(v_a_6509_, 1);
                                    v___x_6511_ =
                                        l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(
                                            v___y_6473_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_6511_) == 0 {
                                        v_isSharedCheck_6519_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6511_)) as u8;
                                        if v_isSharedCheck_6519_ == 0 {
                                            v_unused_6520_ =
                                                crate::leanh::lean_ctor_get(v___x_6511_, 0);
                                            crate::leanh::lean_dec(v_unused_6520_);
                                            v___x_6513_ = v___x_6511_;
                                            v_isShared_6514_ = v_isSharedCheck_6519_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_6511_);
                                            v___x_6513_ = crate::leanh::lean_box(0);
                                            v_isShared_6514_ = v_isSharedCheck_6519_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_val_6510_);
                                        crate::leanh::lean_dec(v_a_6507_);
                                        v_a_6521_ = crate::leanh::lean_ctor_get(v___x_6511_, 0);
                                        v_isSharedCheck_6528_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6511_)) as u8;
                                        if v_isSharedCheck_6528_ == 0 {
                                            v___x_6523_ = v___x_6511_;
                                            v_isShared_6524_ = v_isSharedCheck_6528_;
                                            state = 16;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6521_);
                                            crate::leanh::lean_dec(v___x_6511_);
                                            v___x_6523_ = crate::leanh::lean_box(0);
                                            v_isShared_6524_ = v_isSharedCheck_6528_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6509_);
                                    crate::leanh::lean_inc_ref(v___y_6459_);
                                    crate::leanh::lean_inc_ref(v___y_6470_);
                                    crate::leanh::lean_inc_ref(v___y_6464_);
                                    crate::leanh::lean_inc_ref(v___y_6462_);
                                    crate::leanh::lean_inc_ref(v___y_6465_);
                                    crate::leanh::lean_inc_ref(v___y_6467_);
                                    crate::leanh::lean_inc_ref(v___y_6463_);
                                    crate::leanh::lean_inc_ref(v___y_6466_);
                                    crate::leanh::lean_inc_ref(v___y_6460_);
                                    crate::leanh::lean_inc_ref(v___y_6469_);
                                    crate::leanh::lean_inc_ref(v___y_6468_);
                                    crate::leanh::lean_inc(v_goal_6406_);
                                    v___x_6529_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(v_goal_6406_, v___y_6468_, v___y_6469_, v___y_6460_, v___y_6466_, v___y_6463_, v___y_6467_, v___y_6465_, v___y_6462_, v___y_6464_, v___y_6470_, v___y_6459_, v___y_6461_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                                    if crate::leanh::lean_obj_tag(v___x_6529_) == 0 {
                                        v_a_6530_ = crate::leanh::lean_ctor_get(v___x_6529_, 0);
                                        crate::leanh::lean_inc(v_a_6530_);
                                        crate::leanh::lean_dec_ref_known(v___x_6529_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_6530_) == 1 {
                                            crate::leanh::lean_dec_ref(v___y_6471_);
                                            crate::leanh::lean_dec_ref(v___y_6470_);
                                            crate::leanh::lean_dec_ref(v___y_6469_);
                                            crate::leanh::lean_dec_ref(v___y_6468_);
                                            crate::leanh::lean_dec_ref(v___y_6467_);
                                            crate::leanh::lean_dec_ref(v___y_6466_);
                                            crate::leanh::lean_dec_ref(v___y_6465_);
                                            crate::leanh::lean_dec_ref(v___y_6464_);
                                            crate::leanh::lean_dec_ref(v___y_6463_);
                                            crate::leanh::lean_dec_ref(v___y_6462_);
                                            crate::leanh::lean_dec_ref(v___y_6461_);
                                            crate::leanh::lean_dec_ref(v___y_6460_);
                                            crate::leanh::lean_dec_ref(v___y_6459_);
                                            crate::leanh::lean_dec(v_goal_6406_);
                                            v_val_6531_ = crate::leanh::lean_ctor_get(v_a_6530_, 0);
                                            crate::leanh::lean_inc(v_val_6531_);
                                            crate::leanh::lean_dec_ref_known(v_a_6530_, 1);
                                            v___y_6435_ = v_a_6507_;
                                            v_g_6436_ = v_val_6531_;
                                            v___y_6437_ = v___y_6473_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_6530_);
                                            crate::leanh::lean_inc_ref(v___y_6459_);
                                            crate::leanh::lean_inc_ref(v___y_6464_);
                                            crate::leanh::lean_inc_ref(v___y_6462_);
                                            crate::leanh::lean_inc_ref(v___y_6465_);
                                            crate::leanh::lean_inc_ref(v___y_6460_);
                                            crate::leanh::lean_inc(v_goal_6406_);
                                            v___x_6532_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceProg(v_goal_6406_, v___y_6468_, v___y_6469_, v___y_6460_, v___y_6466_, v___y_6463_, v___y_6467_, v___y_6465_, v___y_6462_, v___y_6464_, v___y_6470_, v___y_6459_, v___y_6461_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                                            crate::leanh::lean_dec_ref(v___y_6461_);
                                            if crate::leanh::lean_obj_tag(v___x_6532_) == 0 {
                                                v_a_6533_ =
                                                    crate::leanh::lean_ctor_get(v___x_6532_, 0);
                                                crate::leanh::lean_inc(v_a_6533_);
                                                crate::leanh::lean_dec_ref_known(v___x_6532_, 1);
                                                if crate::leanh::lean_obj_tag(v_a_6533_) == 1 {
                                                    crate::leanh::lean_dec_ref(v___y_6471_);
                                                    crate::leanh::lean_dec_ref(v___y_6465_);
                                                    crate::leanh::lean_dec_ref(v___y_6464_);
                                                    crate::leanh::lean_dec_ref(v___y_6462_);
                                                    crate::leanh::lean_dec_ref(v___y_6460_);
                                                    crate::leanh::lean_dec_ref(v___y_6459_);
                                                    crate::leanh::lean_dec(v_goal_6406_);
                                                    v_val_6534_ =
                                                        crate::leanh::lean_ctor_get(v_a_6533_, 0);
                                                    crate::leanh::lean_inc(v_val_6534_);
                                                    crate::leanh::lean_dec_ref_known(v_a_6533_, 1);
                                                    v___y_6435_ = v_a_6507_;
                                                    v_g_6436_ = v_val_6534_;
                                                    v___y_6437_ = v___y_6473_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_a_6533_);
                                                    v___x_6535_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_6473_);
                                                    if crate::leanh::lean_obj_tag(v___x_6535_) == 0
                                                    {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_6535_,
                                                            1,
                                                        );
                                                        v___x_6536_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_a_6507_, v_goal_6406_, v___y_6459_, v___y_6471_, v___y_6465_, v___y_6460_, v___y_6462_, v___y_6464_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                                                        return v___x_6536_;
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_6507_);
                                                        crate::leanh::lean_dec_ref(v___y_6471_);
                                                        crate::leanh::lean_dec_ref(v___y_6465_);
                                                        crate::leanh::lean_dec_ref(v___y_6464_);
                                                        crate::leanh::lean_dec_ref(v___y_6462_);
                                                        crate::leanh::lean_dec_ref(v___y_6460_);
                                                        crate::leanh::lean_dec_ref(v___y_6459_);
                                                        crate::leanh::lean_dec(v_goal_6406_);
                                                        v_a_6537_ = crate::leanh::lean_ctor_get(
                                                            v___x_6535_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_6544_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_6535_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_6544_ == 0 {
                                                            v___x_6539_ = v___x_6535_;
                                                            v_isShared_6540_ =
                                                                v_isSharedCheck_6544_;
                                                            state = 18;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_6537_);
                                                            crate::leanh::lean_dec(v___x_6535_);
                                                            v___x_6539_ = crate::leanh::lean_box(0);
                                                            v_isShared_6540_ =
                                                                v_isSharedCheck_6544_;
                                                            state = 18;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_6507_);
                                                crate::leanh::lean_dec_ref(v___y_6471_);
                                                crate::leanh::lean_dec_ref(v___y_6465_);
                                                crate::leanh::lean_dec_ref(v___y_6464_);
                                                crate::leanh::lean_dec_ref(v___y_6462_);
                                                crate::leanh::lean_dec_ref(v___y_6460_);
                                                crate::leanh::lean_dec_ref(v___y_6459_);
                                                crate::leanh::lean_dec(v_goal_6406_);
                                                v_a_6545_ =
                                                    crate::leanh::lean_ctor_get(v___x_6532_, 0);
                                                v_isSharedCheck_6552_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_6532_))
                                                        as u8;
                                                if v_isSharedCheck_6552_ == 0 {
                                                    v___x_6547_ = v___x_6532_;
                                                    v_isShared_6548_ = v_isSharedCheck_6552_;
                                                    state = 20;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_6545_);
                                                    crate::leanh::lean_dec(v___x_6532_);
                                                    v___x_6547_ = crate::leanh::lean_box(0);
                                                    v_isShared_6548_ = v_isSharedCheck_6552_;
                                                    state = 20;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_6507_);
                                        crate::leanh::lean_dec_ref(v___y_6471_);
                                        crate::leanh::lean_dec_ref(v___y_6470_);
                                        crate::leanh::lean_dec_ref(v___y_6469_);
                                        crate::leanh::lean_dec_ref(v___y_6468_);
                                        crate::leanh::lean_dec_ref(v___y_6467_);
                                        crate::leanh::lean_dec_ref(v___y_6466_);
                                        crate::leanh::lean_dec_ref(v___y_6465_);
                                        crate::leanh::lean_dec_ref(v___y_6464_);
                                        crate::leanh::lean_dec_ref(v___y_6463_);
                                        crate::leanh::lean_dec_ref(v___y_6462_);
                                        crate::leanh::lean_dec_ref(v___y_6461_);
                                        crate::leanh::lean_dec_ref(v___y_6460_);
                                        crate::leanh::lean_dec_ref(v___y_6459_);
                                        crate::leanh::lean_dec(v_goal_6406_);
                                        v_a_6553_ = crate::leanh::lean_ctor_get(v___x_6529_, 0);
                                        v_isSharedCheck_6560_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6529_)) as u8;
                                        if v_isSharedCheck_6560_ == 0 {
                                            v___x_6555_ = v___x_6529_;
                                            v_isShared_6556_ = v_isSharedCheck_6560_;
                                            state = 22;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6553_);
                                            crate::leanh::lean_dec(v___x_6529_);
                                            v___x_6555_ = crate::leanh::lean_box(0);
                                            v_isShared_6556_ = v_isSharedCheck_6560_;
                                            state = 22;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6507_);
                                crate::leanh::lean_dec_ref(v___y_6471_);
                                crate::leanh::lean_dec_ref(v___y_6470_);
                                crate::leanh::lean_dec_ref(v___y_6469_);
                                crate::leanh::lean_dec_ref(v___y_6468_);
                                crate::leanh::lean_dec_ref(v___y_6467_);
                                crate::leanh::lean_dec_ref(v___y_6466_);
                                crate::leanh::lean_dec_ref(v___y_6465_);
                                crate::leanh::lean_dec_ref(v___y_6464_);
                                crate::leanh::lean_dec_ref(v___y_6463_);
                                crate::leanh::lean_dec_ref(v___y_6462_);
                                crate::leanh::lean_dec_ref(v___y_6461_);
                                crate::leanh::lean_dec_ref(v___y_6460_);
                                crate::leanh::lean_dec_ref(v___y_6459_);
                                crate::leanh::lean_dec(v_goal_6406_);
                                v_a_6561_ = crate::leanh::lean_ctor_get(v___x_6508_, 0);
                                v_isSharedCheck_6568_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6508_)) as u8;
                                if v_isSharedCheck_6568_ == 0 {
                                    v___x_6563_ = v___x_6508_;
                                    v_isShared_6564_ = v_isSharedCheck_6568_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6561_);
                                    crate::leanh::lean_dec(v___x_6508_);
                                    v___x_6563_ = crate::leanh::lean_box(0);
                                    v_isShared_6564_ = v_isSharedCheck_6568_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_6471_);
                            crate::leanh::lean_dec_ref(v___y_6470_);
                            crate::leanh::lean_dec_ref(v___y_6469_);
                            crate::leanh::lean_dec_ref(v___y_6468_);
                            crate::leanh::lean_dec_ref(v___y_6467_);
                            crate::leanh::lean_dec_ref(v___y_6466_);
                            crate::leanh::lean_dec_ref(v___y_6465_);
                            crate::leanh::lean_dec_ref(v___y_6464_);
                            crate::leanh::lean_dec_ref(v___y_6463_);
                            crate::leanh::lean_dec_ref(v___y_6462_);
                            crate::leanh::lean_dec_ref(v___y_6461_);
                            crate::leanh::lean_dec_ref(v___y_6460_);
                            crate::leanh::lean_dec_ref(v___y_6459_);
                            crate::leanh::lean_dec(v_goal_6406_);
                            v_a_6569_ = crate::leanh::lean_ctor_get(v___x_6506_, 0);
                            v_isSharedCheck_6576_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6506_)) as u8;
                            if v_isSharedCheck_6576_ == 0 {
                                v___x_6571_ = v___x_6506_;
                                v_isShared_6572_ = v_isSharedCheck_6576_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6569_);
                                crate::leanh::lean_dec(v___x_6506_);
                                v___x_6571_ = crate::leanh::lean_box(0);
                                v_isShared_6572_ = v_isSharedCheck_6576_;
                                state = 26;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6471_);
                    crate::leanh::lean_dec_ref(v___y_6470_);
                    crate::leanh::lean_dec_ref(v___y_6469_);
                    crate::leanh::lean_dec_ref(v___y_6468_);
                    crate::leanh::lean_dec_ref(v___y_6467_);
                    crate::leanh::lean_dec_ref(v___y_6466_);
                    crate::leanh::lean_dec_ref(v___y_6465_);
                    crate::leanh::lean_dec_ref(v___y_6464_);
                    crate::leanh::lean_dec_ref(v___y_6463_);
                    crate::leanh::lean_dec_ref(v___y_6462_);
                    crate::leanh::lean_dec_ref(v___y_6461_);
                    crate::leanh::lean_dec_ref(v___y_6460_);
                    crate::leanh::lean_dec_ref(v___y_6459_);
                    crate::leanh::lean_dec_ref(v_scope_6407_);
                    crate::leanh::lean_dec(v_goal_6406_);
                    v_a_6577_ = crate::leanh::lean_ctor_get(v___x_6483_, 0);
                    v_isSharedCheck_6584_ = (!crate::leanh::lean_is_exclusive(v___x_6483_)) as u8;
                    if v_isSharedCheck_6584_ == 0 {
                        v___x_6579_ = v___x_6483_;
                        v_isShared_6580_ = v_isSharedCheck_6584_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6577_);
                        crate::leanh::lean_dec(v___x_6483_);
                        v___x_6579_ = crate::leanh::lean_box(0);
                        v_isShared_6580_ = v_isSharedCheck_6584_;
                        state = 28;
                        continue;
                    }
                }
            }
            10 => {
                v___x_6490_ = crate::leanh::lean_box(0);
                v___x_6491_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6491_, 0, v_val_6485_);
                crate::leanh::lean_ctor_set(v___x_6491_, 1, v___x_6490_);
                v___x_6492_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6492_, 0, v_scope_6407_);
                crate::leanh::lean_ctor_set(v___x_6492_, 1, v___x_6491_);
                if v_isShared_6489_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6488_, 0, v___x_6492_);
                    v___x_6494_ = v___x_6488_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6495_, 0, v___x_6492_);
                    v___x_6494_ = v_reuseFailAlloc_6495_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6494_;
            }
            12 => {
                if v_isShared_6501_ == 0 {
                    v___x_6503_ = v___x_6500_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6498_);
                    v___x_6503_ = v_reuseFailAlloc_6504_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6503_;
            }
            14 => {
                v___x_6515_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6515_, 0, v_a_6507_);
                crate::leanh::lean_ctor_set(v___x_6515_, 1, v_val_6510_);
                if v_isShared_6514_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6513_, 0, v___x_6515_);
                    v___x_6517_ = v___x_6513_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6518_, 0, v___x_6515_);
                    v___x_6517_ = v_reuseFailAlloc_6518_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6517_;
            }
            16 => {
                if v_isShared_6524_ == 0 {
                    v___x_6526_ = v___x_6523_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6521_);
                    v___x_6526_ = v_reuseFailAlloc_6527_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6526_;
            }
            18 => {
                if v_isShared_6540_ == 0 {
                    v___x_6542_ = v___x_6539_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6543_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_a_6537_);
                    v___x_6542_ = v_reuseFailAlloc_6543_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6542_;
            }
            20 => {
                if v_isShared_6548_ == 0 {
                    v___x_6550_ = v___x_6547_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6551_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6551_, 0, v_a_6545_);
                    v___x_6550_ = v_reuseFailAlloc_6551_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6550_;
            }
            22 => {
                if v_isShared_6556_ == 0 {
                    v___x_6558_ = v___x_6555_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_a_6553_);
                    v___x_6558_ = v_reuseFailAlloc_6559_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6558_;
            }
            24 => {
                if v_isShared_6564_ == 0 {
                    v___x_6566_ = v___x_6563_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6567_, 0, v_a_6561_);
                    v___x_6566_ = v_reuseFailAlloc_6567_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6566_;
            }
            26 => {
                if v_isShared_6572_ == 0 {
                    v___x_6574_ = v___x_6571_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_a_6569_);
                    v___x_6574_ = v_reuseFailAlloc_6575_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_6574_;
            }
            28 => {
                if v_isShared_6580_ == 0 {
                    v___x_6582_ = v___x_6579_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6583_, 0, v_a_6577_);
                    v___x_6582_ = v_reuseFailAlloc_6583_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6582_;
            }
            30 => {
                v_options_6595_ = crate::leanh::lean_ctor_get(v___y_6417_, 2);
                v_inheritedTraceOptions_6596_ = crate::leanh::lean_ctor_get(v___y_6417_, 13);
                v_hasTrace_6597_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_6595_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_cls_6598_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                if v_hasTrace_6597_ == 0 {
                    v___y_6600_ = v___y_6408_;
                    v___y_6601_ = v___y_6409_;
                    v___y_6602_ = v___y_6410_;
                    v___y_6603_ = v___y_6411_;
                    v___y_6604_ = v___y_6412_;
                    v___y_6605_ = v___y_6413_;
                    v___y_6606_ = v___y_6414_;
                    v___y_6607_ = v___y_6415_;
                    v___y_6608_ = v___y_6416_;
                    v___y_6609_ = v___y_6417_;
                    v___y_6610_ = v___y_6418_;
                    state = 33;
                    continue;
                } else {
                    v___x_6766_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
                    v___x_6767_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6596_,
                        v_options_6595_,
                        v___x_6766_,
                    );
                    if v___x_6767_ == 0 {
                        v___y_6600_ = v___y_6408_;
                        v___y_6601_ = v___y_6409_;
                        v___y_6602_ = v___y_6410_;
                        v___y_6603_ = v___y_6411_;
                        v___y_6604_ = v___y_6412_;
                        v___y_6605_ = v___y_6413_;
                        v___y_6606_ = v___y_6414_;
                        v___y_6607_ = v___y_6415_;
                        v___y_6608_ = v___y_6416_;
                        v___y_6609_ = v___y_6417_;
                        v___y_6610_ = v___y_6418_;
                        state = 33;
                        continue;
                    } else {
                        v___x_6768_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11);
                        crate::leanh::lean_inc(v_a_6586_);
                        v___x_6769_ = l_Lean_MessageData_ofExpr(v_a_6586_);
                        v___x_6770_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6770_, 0, v___x_6768_);
                        crate::leanh::lean_ctor_set(v___x_6770_, 1, v___x_6769_);
                        v___x_6771_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_6598_, v___x_6770_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_);
                        if crate::leanh::lean_obj_tag(v___x_6771_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6771_, 1);
                            v___y_6600_ = v___y_6408_;
                            v___y_6601_ = v___y_6409_;
                            v___y_6602_ = v___y_6410_;
                            v___y_6603_ = v___y_6411_;
                            v___y_6604_ = v___y_6412_;
                            v___y_6605_ = v___y_6413_;
                            v___y_6606_ = v___y_6414_;
                            v___y_6607_ = v___y_6415_;
                            v___y_6608_ = v___y_6416_;
                            v___y_6609_ = v___y_6417_;
                            v___y_6610_ = v___y_6418_;
                            state = 33;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_6588_);
                            crate::leanh::lean_dec(v_a_6586_);
                            crate::leanh::lean_dec_ref(v_scope_6407_);
                            crate::leanh::lean_dec(v_goal_6406_);
                            v_a_6772_ = crate::leanh::lean_ctor_get(v___x_6771_, 0);
                            v_isSharedCheck_6779_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6771_)) as u8;
                            if v_isSharedCheck_6779_ == 0 {
                                v___x_6774_ = v___x_6771_;
                                v_isShared_6775_ = v_isSharedCheck_6779_;
                                state = 54;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6772_);
                                crate::leanh::lean_dec(v___x_6771_);
                                v___x_6774_ = crate::leanh::lean_box(0);
                                v_isShared_6775_ = v_isSharedCheck_6779_;
                                state = 54;
                                continue;
                            }
                        }
                    }
                }
            }
            31 => {
                v___x_6591_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6591_, 0, v_a_6586_);
                if v_isShared_6589_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6588_, 0, v___x_6591_);
                    v___x_6593_ = v___x_6588_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6594_, 0, v___x_6591_);
                    v___x_6593_ = v_reuseFailAlloc_6594_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_6593_;
            }
            33 => {
                crate::leanh::lean_inc(v_goal_6406_);
                v___x_6611_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(v_goal_6406_, v_a_6586_, v___y_6600_, v___y_6601_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                if crate::leanh::lean_obj_tag(v___x_6611_) == 0 {
                    v_a_6612_ = crate::leanh::lean_ctor_get(v___x_6611_, 0);
                    crate::leanh::lean_inc(v_a_6612_);
                    crate::leanh::lean_dec_ref_known(v___x_6611_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6612_) == 1 {
                        crate::leanh::lean_del_object(v___x_6588_);
                        crate::leanh::lean_dec(v_a_6586_);
                        crate::leanh::lean_dec(v_goal_6406_);
                        v_val_6613_ = crate::leanh::lean_ctor_get(v_a_6612_, 0);
                        crate::leanh::lean_inc(v_val_6613_);
                        crate::leanh::lean_dec_ref_known(v_a_6612_, 1);
                        v_g_6425_ = v_val_6613_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_6612_);
                        crate::leanh::lean_inc(v_goal_6406_);
                        v___x_6614_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(v_goal_6406_, v_a_6586_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                        if crate::leanh::lean_obj_tag(v___x_6614_) == 0 {
                            v_a_6615_ = crate::leanh::lean_ctor_get(v___x_6614_, 0);
                            crate::leanh::lean_inc(v_a_6615_);
                            crate::leanh::lean_dec_ref_known(v___x_6614_, 1);
                            if crate::leanh::lean_obj_tag(v_a_6615_) == 1 {
                                crate::leanh::lean_del_object(v___x_6588_);
                                crate::leanh::lean_dec(v_a_6586_);
                                crate::leanh::lean_dec(v_goal_6406_);
                                v_val_6616_ = crate::leanh::lean_ctor_get(v_a_6615_, 0);
                                crate::leanh::lean_inc(v_val_6616_);
                                crate::leanh::lean_dec_ref_known(v_a_6615_, 1);
                                v_g_6425_ = v_val_6616_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_6615_);
                                crate::leanh::lean_inc(v_goal_6406_);
                                v___x_6617_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(v_goal_6406_, v_a_6586_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                                if crate::leanh::lean_obj_tag(v___x_6617_) == 0 {
                                    v_a_6618_ = crate::leanh::lean_ctor_get(v___x_6617_, 0);
                                    crate::leanh::lean_inc(v_a_6618_);
                                    crate::leanh::lean_dec_ref_known(v___x_6617_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_6618_) == 1 {
                                        crate::leanh::lean_del_object(v___x_6588_);
                                        crate::leanh::lean_dec(v_a_6586_);
                                        crate::leanh::lean_dec(v_goal_6406_);
                                        v_val_6619_ = crate::leanh::lean_ctor_get(v_a_6618_, 0);
                                        crate::leanh::lean_inc(v_val_6619_);
                                        crate::leanh::lean_dec_ref_known(v_a_6618_, 1);
                                        v_g_6425_ = v_val_6619_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_6618_);
                                        crate::leanh::lean_inc(v_goal_6406_);
                                        v___x_6620_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(v_goal_6406_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                                        if crate::leanh::lean_obj_tag(v___x_6620_) == 0 {
                                            v_a_6621_ = crate::leanh::lean_ctor_get(v___x_6620_, 0);
                                            crate::leanh::lean_inc(v_a_6621_);
                                            crate::leanh::lean_dec_ref_known(v___x_6620_, 1);
                                            if crate::leanh::lean_obj_tag(v_a_6621_) == 1 {
                                                crate::leanh::lean_del_object(v___x_6588_);
                                                crate::leanh::lean_dec(v_a_6586_);
                                                crate::leanh::lean_dec(v_goal_6406_);
                                                v_val_6622_ =
                                                    crate::leanh::lean_ctor_get(v_a_6621_, 0);
                                                crate::leanh::lean_inc(v_val_6622_);
                                                crate::leanh::lean_dec_ref_known(v_a_6621_, 1);
                                                v_gs_6421_ = v_val_6622_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_a_6621_);
                                                crate::leanh::lean_inc(v_a_6586_);
                                                v___x_6623_ =
                                                    l_Lean_Expr_cleanupAnnotations(v_a_6586_);
                                                v___x_6624_ = l_Lean_Expr_isApp(v___x_6623_);
                                                if v___x_6624_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_6623_);
                                                    crate::leanh::lean_dec_ref(v_scope_6407_);
                                                    crate::leanh::lean_dec(v_goal_6406_);
                                                    state = 31;
                                                    continue;
                                                } else {
                                                    v_arg_6625_ =
                                                        crate::leanh::lean_ctor_get(v___x_6623_, 1);
                                                    crate::leanh::lean_inc_ref(v_arg_6625_);
                                                    v___x_6626_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_6623_,
                                                    );
                                                    v___x_6627_ = l_Lean_Expr_isApp(v___x_6626_);
                                                    if v___x_6627_ == 0 {
                                                        crate::leanh::lean_dec_ref(v___x_6626_);
                                                        crate::leanh::lean_dec_ref(v_arg_6625_);
                                                        crate::leanh::lean_dec_ref(v_scope_6407_);
                                                        crate::leanh::lean_dec(v_goal_6406_);
                                                        state = 31;
                                                        continue;
                                                    } else {
                                                        v_arg_6628_ = crate::leanh::lean_ctor_get(
                                                            v___x_6626_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc_ref(v_arg_6628_);
                                                        v___x_6629_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_6626_,
                                                            );
                                                        v___x_6630_ =
                                                            l_Lean_Expr_isApp(v___x_6629_);
                                                        if v___x_6630_ == 0 {
                                                            crate::leanh::lean_dec_ref(v___x_6629_);
                                                            crate::leanh::lean_dec_ref(v_arg_6628_);
                                                            crate::leanh::lean_dec_ref(v_arg_6625_);
                                                            crate::leanh::lean_dec_ref(
                                                                v_scope_6407_,
                                                            );
                                                            crate::leanh::lean_dec(v_goal_6406_);
                                                            state = 31;
                                                            continue;
                                                        } else {
                                                            v_arg_6631_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v___x_6629_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_inc_ref(v_arg_6631_);
                                                            v___x_6632_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_6629_,
                                                                );
                                                            v___x_6633_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0;
                                                            v___x_6634_ = l_Lean_Expr_isConstOf(
                                                                v___x_6632_,
                                                                v___x_6633_,
                                                            );
                                                            if v___x_6634_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_6632_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_6631_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_6628_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_6625_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_scope_6407_,
                                                                );
                                                                crate::leanh::lean_dec(
                                                                    v_goal_6406_,
                                                                );
                                                                state = 31;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_del_object(
                                                                    v___x_6588_,
                                                                );
                                                                crate::leanh::lean_dec(v_a_6586_);
                                                                crate::leanh::lean_inc(
                                                                    v_goal_6406_,
                                                                );
                                                                v___x_6635_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(v_goal_6406_, v_arg_6625_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_6635_,
                                                                ) == 0
                                                                {
                                                                    v_a_6636_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_6635_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_6636_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_6635_, 1);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v_a_6636_,
                                                                    ) == 1
                                                                    {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_6632_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_6631_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_6628_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_6625_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_goal_6406_,
                                                                        );
                                                                        v_val_6637_ = crate::leanh::lean_ctor_get(v_a_6636_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_val_6637_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v_a_6636_, 1);
                                                                        v_g_6425_ = v_val_6637_;
                                                                        state = 2;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_dec(
                                                                            v_a_6636_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_6625_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_6628_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_6631_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v___x_6632_,
                                                                        );
                                                                        crate::leanh::lean_inc(
                                                                            v_goal_6406_,
                                                                        );
                                                                        v___x_6638_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(v_goal_6406_, v___x_6632_, v_arg_6631_, v_arg_6628_, v_arg_6625_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                                                                        if crate::leanh::lean_obj_tag(v___x_6638_) == 0 {
v_a_6639_ = crate::leanh::lean_ctor_get(v___x_6638_, 0);
crate::leanh::lean_inc(v_a_6639_);
crate::leanh::lean_dec_ref_known(v___x_6638_, 1);
if crate::leanh::lean_obj_tag(v_a_6639_) == 1 {
crate::leanh::lean_dec_ref(v___x_6632_);
crate::leanh::lean_dec_ref(v_arg_6631_);
crate::leanh::lean_dec_ref(v_arg_6628_);
crate::leanh::lean_dec_ref(v_arg_6625_);
crate::leanh::lean_dec(v_goal_6406_);
v_val_6640_ = crate::leanh::lean_ctor_get(v_a_6639_, 0);
crate::leanh::lean_inc(v_val_6640_);
crate::leanh::lean_dec_ref_known(v_a_6639_, 1);
v_g_6425_ = v_val_6640_;
state = 2; continue;
} else {
crate::leanh::lean_dec(v_a_6639_);
v_dummy_6641_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1);
v_nargs_6642_ = l_Lean_Expr_getAppNumArgs(v_arg_6625_);
crate::leanh::lean_inc(v_nargs_6642_);
v___x_6643_ = lean_mk_array(v_nargs_6642_, v_dummy_6641_);
v___x_6644_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_6645_ = lean_nat_sub(v_nargs_6642_, v___x_6644_);
crate::leanh::lean_dec(v_nargs_6642_);
crate::leanh::lean_inc_ref(v_arg_6625_);
v___x_6646_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__0(v_arg_6625_, v___x_6643_, v___x_6645_);
v_fst_6647_ = crate::leanh::lean_ctor_get(v___x_6646_, 0);
v_snd_6648_ = crate::leanh::lean_ctor_get(v___x_6646_, 1);
v_isSharedCheck_6717_ = (!crate::leanh::lean_is_exclusive(v___x_6646_)) as u8;
if v_isSharedCheck_6717_ == 0 {
v___x_6650_ = v___x_6646_;
v_isShared_6651_ = v_isSharedCheck_6717_;
state = 34; continue;
} else {
crate::leanh::lean_inc(v_snd_6648_);
crate::leanh::lean_inc(v_fst_6647_);
crate::leanh::lean_dec(v___x_6646_);
v___x_6650_ = crate::leanh::lean_box(0);
v_isShared_6651_ = v_isSharedCheck_6717_;
state = 34; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v___x_6632_);
crate::leanh::lean_dec_ref(v_arg_6631_);
crate::leanh::lean_dec_ref(v_arg_6628_);
crate::leanh::lean_dec_ref(v_arg_6625_);
crate::leanh::lean_dec_ref(v_scope_6407_);
crate::leanh::lean_dec(v_goal_6406_);
v_a_6718_ = crate::leanh::lean_ctor_get(v___x_6638_, 0);
v_isSharedCheck_6725_ = (!crate::leanh::lean_is_exclusive(v___x_6638_)) as u8;
if v_isSharedCheck_6725_ == 0 {
v___x_6720_ = v___x_6638_;
v_isShared_6721_ = v_isSharedCheck_6725_;
state = 42; continue;
} else {
crate::leanh::lean_inc(v_a_6718_);
crate::leanh::lean_dec(v___x_6638_);
v___x_6720_ = crate::leanh::lean_box(0);
v_isShared_6721_ = v_isSharedCheck_6725_;
state = 42; continue;
}
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_6632_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_6631_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_6628_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_6625_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_scope_6407_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_goal_6406_,
                                                                    );
                                                                    v_a_6726_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_6635_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_6733_ = (!crate::leanh::lean_is_exclusive(v___x_6635_)) as u8;
                                                                    if v_isSharedCheck_6733_ == 0 {
                                                                        v___x_6728_ = v___x_6635_;
                                                                        v_isShared_6729_ =
                                                                            v_isSharedCheck_6733_;
                                                                        state = 44;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_6726_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_6635_,
                                                                        );
                                                                        v___x_6728_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_6729_ =
                                                                            v_isSharedCheck_6733_;
                                                                        state = 44;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_del_object(v___x_6588_);
                                            crate::leanh::lean_dec(v_a_6586_);
                                            crate::leanh::lean_dec_ref(v_scope_6407_);
                                            crate::leanh::lean_dec(v_goal_6406_);
                                            v_a_6734_ = crate::leanh::lean_ctor_get(v___x_6620_, 0);
                                            v_isSharedCheck_6741_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_6620_))
                                                    as u8;
                                            if v_isSharedCheck_6741_ == 0 {
                                                v___x_6736_ = v___x_6620_;
                                                v_isShared_6737_ = v_isSharedCheck_6741_;
                                                state = 46;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_6734_);
                                                crate::leanh::lean_dec(v___x_6620_);
                                                v___x_6736_ = crate::leanh::lean_box(0);
                                                v_isShared_6737_ = v_isSharedCheck_6741_;
                                                state = 46;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_6588_);
                                    crate::leanh::lean_dec(v_a_6586_);
                                    crate::leanh::lean_dec_ref(v_scope_6407_);
                                    crate::leanh::lean_dec(v_goal_6406_);
                                    v_a_6742_ = crate::leanh::lean_ctor_get(v___x_6617_, 0);
                                    v_isSharedCheck_6749_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6617_)) as u8;
                                    if v_isSharedCheck_6749_ == 0 {
                                        v___x_6744_ = v___x_6617_;
                                        v_isShared_6745_ = v_isSharedCheck_6749_;
                                        state = 48;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6742_);
                                        crate::leanh::lean_dec(v___x_6617_);
                                        v___x_6744_ = crate::leanh::lean_box(0);
                                        v_isShared_6745_ = v_isSharedCheck_6749_;
                                        state = 48;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6588_);
                            crate::leanh::lean_dec(v_a_6586_);
                            crate::leanh::lean_dec_ref(v_scope_6407_);
                            crate::leanh::lean_dec(v_goal_6406_);
                            v_a_6750_ = crate::leanh::lean_ctor_get(v___x_6614_, 0);
                            v_isSharedCheck_6757_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6614_)) as u8;
                            if v_isSharedCheck_6757_ == 0 {
                                v___x_6752_ = v___x_6614_;
                                v_isShared_6753_ = v_isSharedCheck_6757_;
                                state = 50;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6750_);
                                crate::leanh::lean_dec(v___x_6614_);
                                v___x_6752_ = crate::leanh::lean_box(0);
                                v_isShared_6753_ = v_isSharedCheck_6757_;
                                state = 50;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6588_);
                    crate::leanh::lean_dec(v_a_6586_);
                    crate::leanh::lean_dec_ref(v_scope_6407_);
                    crate::leanh::lean_dec(v_goal_6406_);
                    v_a_6758_ = crate::leanh::lean_ctor_get(v___x_6611_, 0);
                    v_isSharedCheck_6765_ = (!crate::leanh::lean_is_exclusive(v___x_6611_)) as u8;
                    if v_isSharedCheck_6765_ == 0 {
                        v___x_6760_ = v___x_6611_;
                        v_isShared_6761_ = v_isSharedCheck_6765_;
                        state = 52;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6758_);
                        crate::leanh::lean_dec(v___x_6611_);
                        v___x_6760_ = crate::leanh::lean_box(0);
                        v_isShared_6761_ = v_isSharedCheck_6765_;
                        state = 52;
                        continue;
                    }
                }
            }
            34 => {
                v___x_6652_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4;
                v___x_6653_ = l_Lean_Expr_isConstOf(v_fst_6647_, v___x_6652_);
                if v___x_6653_ == 0 {
                    crate::leanh::lean_del_object(v___x_6650_);
                    crate::leanh::lean_dec(v_snd_6648_);
                    crate::leanh::lean_dec(v_fst_6647_);
                    crate::leanh::lean_inc_ref(v_arg_6625_);
                    v___x_6654_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails(v_goal_6406_, v___x_6632_, v_arg_6631_, v_arg_6628_, v_arg_6625_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                    crate::leanh::lean_dec_ref(v___x_6632_);
                    if crate::leanh::lean_obj_tag(v___x_6654_) == 0 {
                        v_a_6655_ = crate::leanh::lean_ctor_get(v___x_6654_, 0);
                        v_isSharedCheck_6664_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6654_)) as u8;
                        if v_isSharedCheck_6664_ == 0 {
                            v___x_6657_ = v___x_6654_;
                            v_isShared_6658_ = v_isSharedCheck_6664_;
                            state = 35;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6655_);
                            crate::leanh::lean_dec(v___x_6654_);
                            v___x_6657_ = crate::leanh::lean_box(0);
                            v_isShared_6658_ = v_isSharedCheck_6664_;
                            state = 35;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_6625_);
                        crate::leanh::lean_dec_ref(v_scope_6407_);
                        v_a_6665_ = crate::leanh::lean_ctor_get(v___x_6654_, 0);
                        v_isSharedCheck_6672_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6654_)) as u8;
                        if v_isSharedCheck_6672_ == 0 {
                            v___x_6667_ = v___x_6654_;
                            v_isShared_6668_ = v_isSharedCheck_6672_;
                            state = 37;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6665_);
                            crate::leanh::lean_dec(v___x_6654_);
                            v___x_6667_ = crate::leanh::lean_box(0);
                            v_isShared_6668_ = v_isSharedCheck_6672_;
                            state = 37;
                            continue;
                        }
                    }
                } else {
                    v___x_6673_ = l_Lean_instInhabitedExpr;
                    v___x_6674_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_6675_ = lean_array_get_borrowed(v___x_6673_, v_snd_6648_, v___x_6674_);
                    crate::leanh::lean_inc(v___x_6675_);
                    v___x_6676_ = l_Lean_Expr_cleanupAnnotations(v___x_6675_);
                    v___x_6677_ = l_Lean_Expr_isApp(v___x_6676_);
                    if v___x_6677_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_6676_);
                        crate::leanh::lean_del_object(v___x_6650_);
                        crate::leanh::lean_dec(v_snd_6648_);
                        crate::leanh::lean_dec(v_fst_6647_);
                        crate::leanh::lean_dec_ref(v___x_6632_);
                        crate::leanh::lean_dec_ref(v_arg_6631_);
                        crate::leanh::lean_dec_ref(v_arg_6628_);
                        crate::leanh::lean_dec_ref(v_scope_6407_);
                        crate::leanh::lean_dec(v_goal_6406_);
                        v___y_6431_ = v_arg_6625_;
                        state = 3;
                        continue;
                    } else {
                        v_arg_6678_ = crate::leanh::lean_ctor_get(v___x_6676_, 1);
                        crate::leanh::lean_inc_ref(v_arg_6678_);
                        v___x_6679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6676_);
                        v___x_6680_ = l_Lean_Expr_isApp(v___x_6679_);
                        if v___x_6680_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_6679_);
                            crate::leanh::lean_dec_ref(v_arg_6678_);
                            crate::leanh::lean_del_object(v___x_6650_);
                            crate::leanh::lean_dec(v_snd_6648_);
                            crate::leanh::lean_dec(v_fst_6647_);
                            crate::leanh::lean_dec_ref(v___x_6632_);
                            crate::leanh::lean_dec_ref(v_arg_6631_);
                            crate::leanh::lean_dec_ref(v_arg_6628_);
                            crate::leanh::lean_dec_ref(v_scope_6407_);
                            crate::leanh::lean_dec(v_goal_6406_);
                            v___y_6431_ = v_arg_6625_;
                            state = 3;
                            continue;
                        } else {
                            v_arg_6681_ = crate::leanh::lean_ctor_get(v___x_6679_, 1);
                            crate::leanh::lean_inc_ref(v_arg_6681_);
                            v___x_6682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6679_);
                            v___x_6683_ = l_Lean_Expr_isApp(v___x_6682_);
                            if v___x_6683_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_6682_);
                                crate::leanh::lean_dec_ref(v_arg_6681_);
                                crate::leanh::lean_dec_ref(v_arg_6678_);
                                crate::leanh::lean_del_object(v___x_6650_);
                                crate::leanh::lean_dec(v_snd_6648_);
                                crate::leanh::lean_dec(v_fst_6647_);
                                crate::leanh::lean_dec_ref(v___x_6632_);
                                crate::leanh::lean_dec_ref(v_arg_6631_);
                                crate::leanh::lean_dec_ref(v_arg_6628_);
                                crate::leanh::lean_dec_ref(v_scope_6407_);
                                crate::leanh::lean_dec(v_goal_6406_);
                                v___y_6431_ = v_arg_6625_;
                                state = 3;
                                continue;
                            } else {
                                v_arg_6684_ = crate::leanh::lean_ctor_get(v___x_6682_, 1);
                                crate::leanh::lean_inc_ref(v_arg_6684_);
                                v___x_6685_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6682_);
                                v___x_6686_ = l_Lean_Expr_isApp(v___x_6685_);
                                if v___x_6686_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_6685_);
                                    crate::leanh::lean_dec_ref(v_arg_6684_);
                                    crate::leanh::lean_dec_ref(v_arg_6681_);
                                    crate::leanh::lean_dec_ref(v_arg_6678_);
                                    crate::leanh::lean_del_object(v___x_6650_);
                                    crate::leanh::lean_dec(v_snd_6648_);
                                    crate::leanh::lean_dec(v_fst_6647_);
                                    crate::leanh::lean_dec_ref(v___x_6632_);
                                    crate::leanh::lean_dec_ref(v_arg_6631_);
                                    crate::leanh::lean_dec_ref(v_arg_6628_);
                                    crate::leanh::lean_dec_ref(v_scope_6407_);
                                    crate::leanh::lean_dec(v_goal_6406_);
                                    v___y_6431_ = v_arg_6625_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_arg_6687_ = crate::leanh::lean_ctor_get(v___x_6685_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_6687_);
                                    v___x_6688_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6685_);
                                    v___x_6689_ = l_Lean_Expr_isApp(v___x_6688_);
                                    if v___x_6689_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_6688_);
                                        crate::leanh::lean_dec_ref(v_arg_6687_);
                                        crate::leanh::lean_dec_ref(v_arg_6684_);
                                        crate::leanh::lean_dec_ref(v_arg_6681_);
                                        crate::leanh::lean_dec_ref(v_arg_6678_);
                                        crate::leanh::lean_del_object(v___x_6650_);
                                        crate::leanh::lean_dec(v_snd_6648_);
                                        crate::leanh::lean_dec(v_fst_6647_);
                                        crate::leanh::lean_dec_ref(v___x_6632_);
                                        crate::leanh::lean_dec_ref(v_arg_6631_);
                                        crate::leanh::lean_dec_ref(v_arg_6628_);
                                        crate::leanh::lean_dec_ref(v_scope_6407_);
                                        crate::leanh::lean_dec(v_goal_6406_);
                                        v___y_6431_ = v_arg_6625_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v_arg_6690_ = crate::leanh::lean_ctor_get(v___x_6688_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_6690_);
                                        v___x_6691_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_6688_);
                                        v___x_6692_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7;
                                        v___x_6693_ =
                                            l_Lean_Expr_isConstOf(v___x_6691_, v___x_6692_);
                                        if v___x_6693_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_6691_);
                                            crate::leanh::lean_dec_ref(v_arg_6690_);
                                            crate::leanh::lean_dec_ref(v_arg_6687_);
                                            crate::leanh::lean_dec_ref(v_arg_6684_);
                                            crate::leanh::lean_dec_ref(v_arg_6681_);
                                            crate::leanh::lean_dec_ref(v_arg_6678_);
                                            crate::leanh::lean_del_object(v___x_6650_);
                                            crate::leanh::lean_dec(v_snd_6648_);
                                            crate::leanh::lean_dec(v_fst_6647_);
                                            crate::leanh::lean_dec_ref(v___x_6632_);
                                            crate::leanh::lean_dec_ref(v_arg_6631_);
                                            crate::leanh::lean_dec_ref(v_arg_6628_);
                                            crate::leanh::lean_dec_ref(v_scope_6407_);
                                            crate::leanh::lean_dec(v_goal_6406_);
                                            v___y_6431_ = v_arg_6625_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v_arg_6625_);
                                            v_options_6694_ =
                                                crate::leanh::lean_ctor_get(v___y_6609_, 2);
                                            v_inheritedTraceOptions_6695_ =
                                                crate::leanh::lean_ctor_get(v___y_6609_, 13);
                                            v_hasTrace_6696_ = crate::leanh::lean_ctor_get_uint8(
                                                v_options_6694_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 1)
                                                    as u32,
                                            );
                                            v___x_6697_ = crate::leanh::lean_unsigned_to_nat(4);
                                            v___x_6698_ = lean_array_get_size(v_snd_6648_);
                                            v___x_6699_ = l_Array_extract___redArg(
                                                v_snd_6648_,
                                                v___x_6697_,
                                                v___x_6698_,
                                            );
                                            v___x_6700_ = l_Lean_Expr_getAppFn(v_arg_6678_);
                                            if v_hasTrace_6696_ == 0 {
                                                crate::leanh::lean_del_object(v___x_6650_);
                                                v___y_6459_ = v_arg_6678_;
                                                v___y_6460_ = v_arg_6631_;
                                                v___y_6461_ = v___x_6700_;
                                                v___y_6462_ = v_arg_6687_;
                                                v___y_6463_ = v_snd_6648_;
                                                v___y_6464_ = v_arg_6684_;
                                                v___y_6465_ = v_arg_6690_;
                                                v___y_6466_ = v___x_6632_;
                                                v___y_6467_ = v___x_6691_;
                                                v___y_6468_ = v_fst_6647_;
                                                v___y_6469_ = v_arg_6628_;
                                                v___y_6470_ = v_arg_6681_;
                                                v___y_6471_ = v___x_6699_;
                                                v___y_6472_ = v___y_6600_;
                                                v___y_6473_ = v___y_6601_;
                                                v___y_6474_ = v___y_6602_;
                                                v___y_6475_ = v___y_6603_;
                                                v___y_6476_ = v___y_6604_;
                                                v___y_6477_ = v___y_6605_;
                                                v___y_6478_ = v___y_6606_;
                                                v___y_6479_ = v___y_6607_;
                                                v___y_6480_ = v___y_6608_;
                                                v___y_6481_ = v___y_6609_;
                                                v___y_6482_ = v___y_6610_;
                                                state = 9;
                                                continue;
                                            } else {
                                                v___x_6701_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
                                                v___x_6702_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6695_, v_options_6694_, v___x_6701_);
                                                if v___x_6702_ == 0 {
                                                    crate::leanh::lean_del_object(v___x_6650_);
                                                    v___y_6459_ = v_arg_6678_;
                                                    v___y_6460_ = v_arg_6631_;
                                                    v___y_6461_ = v___x_6700_;
                                                    v___y_6462_ = v_arg_6687_;
                                                    v___y_6463_ = v_snd_6648_;
                                                    v___y_6464_ = v_arg_6684_;
                                                    v___y_6465_ = v_arg_6690_;
                                                    v___y_6466_ = v___x_6632_;
                                                    v___y_6467_ = v___x_6691_;
                                                    v___y_6468_ = v_fst_6647_;
                                                    v___y_6469_ = v_arg_6628_;
                                                    v___y_6470_ = v_arg_6681_;
                                                    v___y_6471_ = v___x_6699_;
                                                    v___y_6472_ = v___y_6600_;
                                                    v___y_6473_ = v___y_6601_;
                                                    v___y_6474_ = v___y_6602_;
                                                    v___y_6475_ = v___y_6603_;
                                                    v___y_6476_ = v___y_6604_;
                                                    v___y_6477_ = v___y_6605_;
                                                    v___y_6478_ = v___y_6606_;
                                                    v___y_6479_ = v___y_6607_;
                                                    v___y_6480_ = v___y_6608_;
                                                    v___y_6481_ = v___y_6609_;
                                                    v___y_6482_ = v___y_6610_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    v___x_6703_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9);
                                                    crate::leanh::lean_inc_ref(v_arg_6678_);
                                                    v___x_6704_ =
                                                        l_Lean_MessageData_ofExpr(v_arg_6678_);
                                                    if v_isShared_6651_ == 0 {
                                                        crate::leanh::lean_ctor_set_tag(
                                                            v___x_6650_,
                                                            7,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_6650_,
                                                            1,
                                                            v___x_6704_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_6650_,
                                                            0,
                                                            v___x_6703_,
                                                        );
                                                        v___x_6706_ = v___x_6650_;
                                                        state = 39;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_6716_ =
                                                            crate::leanh::lean_alloc_ctor(
                                                                7,
                                                                2,
                                                                (0) as u32,
                                                            );
                                                        crate::leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_6716_,
                                                            0,
                                                            v___x_6703_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_6716_,
                                                            1,
                                                            v___x_6704_,
                                                        );
                                                        v___x_6706_ = v_reuseFailAlloc_6716_;
                                                        state = 39;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            35 => {
                if crate::leanh::lean_obj_tag(v_a_6655_) == 1 {
                    crate::leanh::lean_del_object(v___x_6657_);
                    crate::leanh::lean_dec_ref(v_arg_6625_);
                    v_val_6659_ = crate::leanh::lean_ctor_get(v_a_6655_, 0);
                    crate::leanh::lean_inc(v_val_6659_);
                    crate::leanh::lean_dec_ref_known(v_a_6655_, 1);
                    v_gs_6421_ = v_val_6659_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_6655_);
                    crate::leanh::lean_dec_ref(v_scope_6407_);
                    v___x_6660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6660_, 0, v_arg_6625_);
                    if v_isShared_6658_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6657_, 0, v___x_6660_);
                        v___x_6662_ = v___x_6657_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_6663_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6663_, 0, v___x_6660_);
                        v___x_6662_ = v_reuseFailAlloc_6663_;
                        state = 36;
                        continue;
                    }
                }
            }
            36 => {
                return v___x_6662_;
            }
            37 => {
                if v_isShared_6668_ == 0 {
                    v___x_6670_ = v___x_6667_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_6671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6671_, 0, v_a_6665_);
                    v___x_6670_ = v_reuseFailAlloc_6671_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_6670_;
            }
            39 => {
                v___x_6707_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_6598_, v___x_6706_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                if crate::leanh::lean_obj_tag(v___x_6707_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6707_, 1);
                    v___y_6459_ = v_arg_6678_;
                    v___y_6460_ = v_arg_6631_;
                    v___y_6461_ = v___x_6700_;
                    v___y_6462_ = v_arg_6687_;
                    v___y_6463_ = v_snd_6648_;
                    v___y_6464_ = v_arg_6684_;
                    v___y_6465_ = v_arg_6690_;
                    v___y_6466_ = v___x_6632_;
                    v___y_6467_ = v___x_6691_;
                    v___y_6468_ = v_fst_6647_;
                    v___y_6469_ = v_arg_6628_;
                    v___y_6470_ = v_arg_6681_;
                    v___y_6471_ = v___x_6699_;
                    v___y_6472_ = v___y_6600_;
                    v___y_6473_ = v___y_6601_;
                    v___y_6474_ = v___y_6602_;
                    v___y_6475_ = v___y_6603_;
                    v___y_6476_ = v___y_6604_;
                    v___y_6477_ = v___y_6605_;
                    v___y_6478_ = v___y_6606_;
                    v___y_6479_ = v___y_6607_;
                    v___y_6480_ = v___y_6608_;
                    v___y_6481_ = v___y_6609_;
                    v___y_6482_ = v___y_6610_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_6700_);
                    crate::leanh::lean_dec_ref(v___x_6699_);
                    crate::leanh::lean_dec_ref(v___x_6691_);
                    crate::leanh::lean_dec_ref(v_arg_6690_);
                    crate::leanh::lean_dec_ref(v_arg_6687_);
                    crate::leanh::lean_dec_ref(v_arg_6684_);
                    crate::leanh::lean_dec_ref(v_arg_6681_);
                    crate::leanh::lean_dec_ref(v_arg_6678_);
                    crate::leanh::lean_dec(v_snd_6648_);
                    crate::leanh::lean_dec(v_fst_6647_);
                    crate::leanh::lean_dec_ref(v___x_6632_);
                    crate::leanh::lean_dec_ref(v_arg_6631_);
                    crate::leanh::lean_dec_ref(v_arg_6628_);
                    crate::leanh::lean_dec_ref(v_scope_6407_);
                    crate::leanh::lean_dec(v_goal_6406_);
                    v_a_6708_ = crate::leanh::lean_ctor_get(v___x_6707_, 0);
                    v_isSharedCheck_6715_ = (!crate::leanh::lean_is_exclusive(v___x_6707_)) as u8;
                    if v_isSharedCheck_6715_ == 0 {
                        v___x_6710_ = v___x_6707_;
                        v_isShared_6711_ = v_isSharedCheck_6715_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6708_);
                        crate::leanh::lean_dec(v___x_6707_);
                        v___x_6710_ = crate::leanh::lean_box(0);
                        v_isShared_6711_ = v_isSharedCheck_6715_;
                        state = 40;
                        continue;
                    }
                }
            }
            40 => {
                if v_isShared_6711_ == 0 {
                    v___x_6713_ = v___x_6710_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_6714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6714_, 0, v_a_6708_);
                    v___x_6713_ = v_reuseFailAlloc_6714_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_6713_;
            }
            42 => {
                if v_isShared_6721_ == 0 {
                    v___x_6723_ = v___x_6720_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_6724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 0, v_a_6718_);
                    v___x_6723_ = v_reuseFailAlloc_6724_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_6723_;
            }
            44 => {
                if v_isShared_6729_ == 0 {
                    v___x_6731_ = v___x_6728_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_6732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 0, v_a_6726_);
                    v___x_6731_ = v_reuseFailAlloc_6732_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_6731_;
            }
            46 => {
                if v_isShared_6737_ == 0 {
                    v___x_6739_ = v___x_6736_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_6740_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6740_, 0, v_a_6734_);
                    v___x_6739_ = v_reuseFailAlloc_6740_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_6739_;
            }
            48 => {
                if v_isShared_6745_ == 0 {
                    v___x_6747_ = v___x_6744_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_6748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6748_, 0, v_a_6742_);
                    v___x_6747_ = v_reuseFailAlloc_6748_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_6747_;
            }
            50 => {
                if v_isShared_6753_ == 0 {
                    v___x_6755_ = v___x_6752_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_6756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6756_, 0, v_a_6750_);
                    v___x_6755_ = v_reuseFailAlloc_6756_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_6755_;
            }
            52 => {
                if v_isShared_6761_ == 0 {
                    v___x_6763_ = v___x_6760_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_6764_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6764_, 0, v_a_6758_);
                    v___x_6763_ = v_reuseFailAlloc_6764_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_6763_;
            }
            54 => {
                if v_isShared_6775_ == 0 {
                    v___x_6777_ = v___x_6774_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_6778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6778_, 0, v_a_6772_);
                    v___x_6777_ = v_reuseFailAlloc_6778_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_6777_;
            }
            56 => {
                if v_isShared_6784_ == 0 {
                    v___x_6786_ = v___x_6783_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_6787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6787_, 0, v_a_6781_);
                    v___x_6786_ = v_reuseFailAlloc_6787_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_6786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(
    mut v_goal_6789_: *mut crate::leanh::LeanObject,
    mut v_scope_6790_: *mut crate::leanh::LeanObject,
    mut v___y_6791_: *mut crate::leanh::LeanObject,
    mut v___y_6792_: *mut crate::leanh::LeanObject,
    mut v___y_6793_: *mut crate::leanh::LeanObject,
    mut v___y_6794_: *mut crate::leanh::LeanObject,
    mut v___y_6795_: *mut crate::leanh::LeanObject,
    mut v___y_6796_: *mut crate::leanh::LeanObject,
    mut v___y_6797_: *mut crate::leanh::LeanObject,
    mut v___y_6798_: *mut crate::leanh::LeanObject,
    mut v___y_6799_: *mut crate::leanh::LeanObject,
    mut v___y_6800_: *mut crate::leanh::LeanObject,
    mut v___y_6801_: *mut crate::leanh::LeanObject,
    mut v___y_6802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6803_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(
        v_goal_6789_,
        v_scope_6790_,
        v___y_6791_,
        v___y_6792_,
        v___y_6793_,
        v___y_6794_,
        v___y_6795_,
        v___y_6796_,
        v___y_6797_,
        v___y_6798_,
        v___y_6799_,
        v___y_6800_,
        v___y_6801_,
    );
    crate::leanh::lean_dec(v___y_6801_);
    crate::leanh::lean_dec_ref(v___y_6800_);
    crate::leanh::lean_dec(v___y_6799_);
    crate::leanh::lean_dec_ref(v___y_6798_);
    crate::leanh::lean_dec(v___y_6797_);
    crate::leanh::lean_dec_ref(v___y_6796_);
    crate::leanh::lean_dec(v___y_6795_);
    crate::leanh::lean_dec_ref(v___y_6794_);
    crate::leanh::lean_dec(v___y_6793_);
    crate::leanh::lean_dec(v___y_6792_);
    crate::leanh::lean_dec_ref(v___y_6791_);
    return v_res_6803_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(
    mut v_scope_6804_: *mut crate::leanh::LeanObject,
    mut v_goal_6805_: *mut crate::leanh::LeanObject,
    mut v_a_6806_: *mut crate::leanh::LeanObject,
    mut v_a_6807_: *mut crate::leanh::LeanObject,
    mut v_a_6808_: *mut crate::leanh::LeanObject,
    mut v_a_6809_: *mut crate::leanh::LeanObject,
    mut v_a_6810_: *mut crate::leanh::LeanObject,
    mut v_a_6811_: *mut crate::leanh::LeanObject,
    mut v_a_6812_: *mut crate::leanh::LeanObject,
    mut v_a_6813_: *mut crate::leanh::LeanObject,
    mut v_a_6814_: *mut crate::leanh::LeanObject,
    mut v_a_6815_: *mut crate::leanh::LeanObject,
    mut v_a_6816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_goal_6805_);
    v___f_6818_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed as *mut core::ffi::c_void,
        14,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6818_, 0, v_goal_6805_);
    crate::leanh::lean_closure_set(v___f_6818_, 1, v_scope_6804_);
    v___x_6819_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_goal_6805_, v___f_6818_, v_a_6806_, v_a_6807_, v_a_6808_, v_a_6809_, v_a_6810_, v_a_6811_, v_a_6812_, v_a_6813_, v_a_6814_, v_a_6815_, v_a_6816_);
    return v___x_6819_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(
    mut v_scope_6820_: *mut crate::leanh::LeanObject,
    mut v_goal_6821_: *mut crate::leanh::LeanObject,
    mut v_a_6822_: *mut crate::leanh::LeanObject,
    mut v_a_6823_: *mut crate::leanh::LeanObject,
    mut v_a_6824_: *mut crate::leanh::LeanObject,
    mut v_a_6825_: *mut crate::leanh::LeanObject,
    mut v_a_6826_: *mut crate::leanh::LeanObject,
    mut v_a_6827_: *mut crate::leanh::LeanObject,
    mut v_a_6828_: *mut crate::leanh::LeanObject,
    mut v_a_6829_: *mut crate::leanh::LeanObject,
    mut v_a_6830_: *mut crate::leanh::LeanObject,
    mut v_a_6831_: *mut crate::leanh::LeanObject,
    mut v_a_6832_: *mut crate::leanh::LeanObject,
    mut v_a_6833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6834_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(
        v_scope_6820_,
        v_goal_6821_,
        v_a_6822_,
        v_a_6823_,
        v_a_6824_,
        v_a_6825_,
        v_a_6826_,
        v_a_6827_,
        v_a_6828_,
        v_a_6829_,
        v_a_6830_,
        v_a_6831_,
        v_a_6832_,
    );
    crate::leanh::lean_dec(v_a_6832_);
    crate::leanh::lean_dec_ref(v_a_6831_);
    crate::leanh::lean_dec(v_a_6830_);
    crate::leanh::lean_dec_ref(v_a_6829_);
    crate::leanh::lean_dec(v_a_6828_);
    crate::leanh::lean_dec_ref(v_a_6827_);
    crate::leanh::lean_dec(v_a_6826_);
    crate::leanh::lean_dec_ref(v_a_6825_);
    crate::leanh::lean_dec(v_a_6824_);
    crate::leanh::lean_dec(v_a_6823_);
    crate::leanh::lean_dec_ref(v_a_6822_);
    return v_res_6834_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
}

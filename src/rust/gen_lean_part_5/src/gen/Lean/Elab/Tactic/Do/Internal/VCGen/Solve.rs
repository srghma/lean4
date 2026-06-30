// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Solve
// Imports: Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache Lean.Elab.Tactic.Do.Internal.VCGen.Entails Lean.Meta.Sym.InstantiateS
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_set, lean_array_to_list, lean_infer_type,
    lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
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
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [102, 111, 114, 97, 108, 108, 115, 32, 105, 110, 32, 96, 115, 111, 108, 118, 101, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 116, 45, 105, 110, 116, 114, 111, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [118, 99, 103, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2_value) as *mut leanh::LeanObject,12843180897352504333 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3_value) as *mut leanh::LeanObject,17186385980065365684 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut leanh::LeanObject,6272605754531080404 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5_value) as *mut leanh::LeanObject,15978311213600074545 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [108, 101, 116, 45, 122, 101, 116, 97, 45, 100, 117, 112, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12_value: leanh::LeanStringObject<104> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 104, m_capacity: 104, m_length: 103, m_data: [109, 118, 99, 103, 101, 110, 39, 58, 32, 115, 104, 97, 114, 101, 100, 45, 99, 111, 110, 116, 105, 110, 117, 97, 116, 105, 111, 110, 32, 104, 97, 110, 100, 108, 105, 110, 103, 32, 102, 111, 114, 32, 96, 95, 95, 100, 111, 95, 106, 112, 96, 32, 105, 115, 32, 110, 111, 116, 32, 121, 101, 116, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 46, 32, 68, 101, 116, 101, 99, 116, 105, 111, 110, 32, 112, 111, 105, 110, 116, 32, 114, 101, 97, 99, 104, 101, 100, 32, 97, 116, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14_value: leanh::LeanStringObject<205> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 205, m_capacity: 205, m_length: 204, m_data: [59, 32, 116, 104, 101, 32, 117, 112, 115, 116, 114, 101, 97, 109, 32, 96, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 111, 110, 74, 111, 105, 110, 80, 111, 105, 110, 116, 96, 32, 40, 96, 115, 114, 99, 47, 76, 101, 97, 110, 47, 69, 108, 97, 98, 47, 84, 97, 99, 116, 105, 99, 47, 68, 111, 47, 86, 67, 71, 101, 110, 46, 108, 101, 97, 110, 58, 50, 49, 53, 96, 41, 32, 110, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 32, 112, 111, 114, 116, 101, 100, 32, 116, 111, 32, 116, 104, 101, 32, 119, 111, 114, 107, 108, 105, 115, 116, 32, 115, 116, 121, 108, 101, 46, 32, 68, 114, 111, 112, 32, 96, 40, 106, 112, 32, 58, 61, 32, 116, 114, 117, 101, 41, 96, 32, 116, 111, 32, 102, 97, 108, 108, 32, 98, 97, 99, 107, 32, 116, 111, 32, 116, 104, 101, 32, 100, 101, 102, 97, 117, 108, 116, 32, 122, 101, 116, 97, 45, 117, 110, 102, 111, 108, 100, 32, 98, 101, 104, 97, 118, 105, 111, 117, 114, 46, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1_value) as *mut leanh::LeanObject,11963640885769744415 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [65, 112, 112, 108, 121, 105, 110, 103, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 80, 114, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 110, 116, 97, 105, 108, 115, 95, 99, 111, 110, 115, 95, 105, 110, 116, 114, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value) as *mut leanh::LeanObject,13332341187416043682 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3_value) as *mut leanh::LeanObject,16895493190937329785 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 116, 111, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [32, 102, 97, 105, 108, 101, 100, 46, 32, 73, 116, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 46, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 110, 116, 97, 105, 108, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 101, 102, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value) as *mut leanh::LeanObject,13332341187416043682 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__0_value) as *mut leanh::LeanObject,515334035361346902 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__1_value) as *mut leanh::LeanObject,1565800902179044421 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__3_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [83, 111, 108, 118, 101, 100, 32, 98, 121, 32, 114, 102, 108, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__5_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 114, 121, 105, 110, 103, 32, 114, 102, 108, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 116, 45, 104, 111, 105, 115, 116, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0: u64 = 0;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 112, 108, 105, 116, 32, 114, 117, 108, 101, 32, 102, 111, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 115, 112, 108, 105, 116, 32, 114, 117, 108, 101, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [102, 118, 97, 114, 45, 122, 101, 116, 97, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 112, 101, 99, 32, 114, 117, 108, 101, 32, 102, 111, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 114, 117, 108, 101, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [78, 101, 101, 100, 101, 100, 32, 115, 116, 97, 116, 101, 32, 105, 110, 116, 114, 111, 46, 32, 82, 101, 116, 114, 121, 105, 110, 103, 46, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [82, 117, 108, 101, 32, 116, 121, 112, 101, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [83, 112, 101, 99, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 103, 108, 111, 98, 97, 108, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 108, 111, 99, 97, 108, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 115, 116, 120, 32, 95, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed as *const core::ffi::c_void, m_arity: 14, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [65, 112, 112, 108, 121, 105, 110, 103, 32, 97, 32, 115, 112, 101, 99, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [46, 32, 69, 120, 99, 101, 115, 115, 32, 97, 114, 103, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value) as *mut leanh::LeanObject,13332341187416043682 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__0_value) as *mut leanh::LeanObject,515334035361346902 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
        14660636995802757424 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_value)
            as *mut leanh::LeanObject,
        11849051038469469124 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_value)
            as *mut leanh::LeanObject,
        6757038018435374033 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value)
            as *mut leanh::LeanObject,
        17511313520436183663 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx(
    mut v_x_3418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3418_) {
        0 => {
            let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3419_ = leanh::lean_unsigned_to_nat(0);
            return v___x_3419_;
        }
        1 => {
            let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3420_ = leanh::lean_unsigned_to_nat(1);
            return v___x_3420_;
        }
        2 => {
            let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3421_ = leanh::lean_unsigned_to_nat(2);
            return v___x_3421_;
        }
        3 => {
            let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3422_ = leanh::lean_unsigned_to_nat(3);
            return v___x_3422_;
        }
        _ => {
            let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3423_ = leanh::lean_unsigned_to_nat(4);
            return v___x_3423_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx___boxed(
    mut v_x_3424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx(v_x_3424_);
    leanh::lean_dec_ref(v_x_3424_);
    return v_res_3425_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
    mut v_t_3426_: *mut leanh::LeanObject,
    mut v_k_3427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_3426_) {
        3 => {
            let mut v_e_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_monad_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_thms_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_e_3428_ = leanh::lean_ctor_get(v_t_3426_, 0);
            leanh::lean_inc_ref(v_e_3428_);
            v_monad_3429_ = leanh::lean_ctor_get(v_t_3426_, 1);
            leanh::lean_inc_ref(v_monad_3429_);
            v_thms_3430_ = leanh::lean_ctor_get(v_t_3426_, 2);
            leanh::lean_inc_ref(v_thms_3430_);
            leanh::lean_dec_ref_known(v_t_3426_, 3);
            v___x_3431_ =
                leanh::lean_apply_3(v_k_3427_, v_e_3428_, v_monad_3429_, v_thms_3430_);
            return v___x_3431_;
        }
        4 => {
            let mut v_scope_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_subgoals_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_scope_3432_ = leanh::lean_ctor_get(v_t_3426_, 0);
            leanh::lean_inc_ref(v_scope_3432_);
            v_subgoals_3433_ = leanh::lean_ctor_get(v_t_3426_, 1);
            leanh::lean_inc(v_subgoals_3433_);
            leanh::lean_dec_ref_known(v_t_3426_, 2);
            v___x_3434_ = leanh::lean_apply_2(v_k_3427_, v_scope_3432_, v_subgoals_3433_);
            return v___x_3434_;
        }
        _ => {
            let mut v_target_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_target_3435_ = leanh::lean_ctor_get(v_t_3426_, 0);
            leanh::lean_inc_ref(v_target_3435_);
            leanh::lean_dec_ref(v_t_3426_);
            v___x_3436_ = leanh::lean_apply_1(v_k_3427_, v_target_3435_);
            return v___x_3436_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim(
    mut v_motive_3437_: *mut leanh::LeanObject,
    mut v_ctorIdx_3438_: *mut leanh::LeanObject,
    mut v_t_3439_: *mut leanh::LeanObject,
    mut v_h_3440_: *mut leanh::LeanObject,
    mut v_k_3441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3442_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_3439_, v_k_3441_);
    return v___x_3442_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___boxed(
    mut v_motive_3443_: *mut leanh::LeanObject,
    mut v_ctorIdx_3444_: *mut leanh::LeanObject,
    mut v_t_3445_: *mut leanh::LeanObject,
    mut v_h_3446_: *mut leanh::LeanObject,
    mut v_k_3447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim(
        v_motive_3443_,
        v_ctorIdx_3444_,
        v_t_3445_,
        v_h_3446_,
        v_k_3447_,
    );
    leanh::lean_dec(v_ctorIdx_3444_);
    return v_res_3448_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noEntailment_elim___redArg(
    mut v_t_3449_: *mut leanh::LeanObject,
    mut v_noEntailment_3450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3451_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3449_,
        v_noEntailment_3450_,
    );
    return v___x_3451_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noEntailment_elim(
    mut v_motive_3452_: *mut leanh::LeanObject,
    mut v_t_3453_: *mut leanh::LeanObject,
    mut v_h_3454_: *mut leanh::LeanObject,
    mut v_noEntailment_3455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3453_,
        v_noEntailment_3455_,
    );
    return v___x_3456_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noProgramFoundInTarget_elim___redArg(
    mut v_t_3457_: *mut leanh::LeanObject,
    mut v_noProgramFoundInTarget_3458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3459_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3457_,
        v_noProgramFoundInTarget_3458_,
    );
    return v___x_3459_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noProgramFoundInTarget_elim(
    mut v_motive_3460_: *mut leanh::LeanObject,
    mut v_t_3461_: *mut leanh::LeanObject,
    mut v_h_3462_: *mut leanh::LeanObject,
    mut v_noProgramFoundInTarget_3463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3464_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3461_,
        v_noProgramFoundInTarget_3463_,
    );
    return v___x_3464_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noStrategyForProgram_elim___redArg(
    mut v_t_3465_: *mut leanh::LeanObject,
    mut v_noStrategyForProgram_3466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3467_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3465_,
        v_noStrategyForProgram_3466_,
    );
    return v___x_3467_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noStrategyForProgram_elim(
    mut v_motive_3468_: *mut leanh::LeanObject,
    mut v_t_3469_: *mut leanh::LeanObject,
    mut v_h_3470_: *mut leanh::LeanObject,
    mut v_noStrategyForProgram_3471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3472_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3469_,
        v_noStrategyForProgram_3471_,
    );
    return v___x_3472_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noSpecFoundForProgram_elim___redArg(
    mut v_t_3473_: *mut leanh::LeanObject,
    mut v_noSpecFoundForProgram_3474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3475_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3473_,
        v_noSpecFoundForProgram_3474_,
    );
    return v___x_3475_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noSpecFoundForProgram_elim(
    mut v_motive_3476_: *mut leanh::LeanObject,
    mut v_t_3477_: *mut leanh::LeanObject,
    mut v_h_3478_: *mut leanh::LeanObject,
    mut v_noSpecFoundForProgram_3479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3480_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3477_,
        v_noSpecFoundForProgram_3479_,
    );
    return v___x_3480_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim___redArg(
    mut v_t_3481_: *mut leanh::LeanObject,
    mut v_goals_3482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3483_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3481_,
        v_goals_3482_,
    );
    return v___x_3483_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim(
    mut v_motive_3484_: *mut leanh::LeanObject,
    mut v_t_3485_: *mut leanh::LeanObject,
    mut v_h_3486_: *mut leanh::LeanObject,
    mut v_goals_3487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3488_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(
        v_t_3485_,
        v_goals_3487_,
    );
    return v___x_3488_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(
    mut v_e_3494_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3497_: u8 = 0;
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: u8 = 0;
    let mut v_expr_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_3494_) {
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
                    v_expr_3500_ = leanh::lean_ctor_get(v_e_3494_, 1);
                    v_e_3494_ = v_expr_3500_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_struct_3502_ = leanh::lean_ctor_get(v_e_3494_, 2);
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
    mut v_e_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3506_: u8 = 0;
    let mut v_r_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3506_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_e_3505_);
    leanh::lean_dec_ref(v_e_3505_);
    v_r_3507_ = leanh::lean_box((v_res_3506_) as usize);
    return v_r_3507_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3509_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0;
    v___x_3510_ = l_Lean_stringToMessageData(v___x_3509_);
    return v___x_3510_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(
    mut v_goal_3511_: *mut leanh::LeanObject,
    mut v_target_3512_: *mut leanh::LeanObject,
    mut v_a_3513_: *mut leanh::LeanObject,
    mut v_a_3514_: *mut leanh::LeanObject,
    mut v_a_3515_: *mut leanh::LeanObject,
    mut v_a_3516_: *mut leanh::LeanObject,
    mut v_a_3517_: *mut leanh::LeanObject,
    mut v_a_3518_: *mut leanh::LeanObject,
    mut v_a_3519_: *mut leanh::LeanObject,
    mut v_a_3520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3530_: u8 = 0;
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3535_: u8 = 0;
    let mut v_a_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3522_ = l_Lean_Expr_isForall(v_target_3512_);
                if v___x_3522_ == 0 {
                    leanh::lean_dec(v_goal_3511_);
                    v___x_3523_ = leanh::lean_box(0);
                    v___x_3524_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3524_, 0, v___x_3523_);
                    return v___x_3524_;
                } else {
                    v___x_3525_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1);
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
                    if leanh::lean_obj_tag(v___x_3526_) == 0 {
                        v_a_3527_ = leanh::lean_ctor_get(v___x_3526_, 0);
                        v_isSharedCheck_3535_ =
                            (!leanh::lean_is_exclusive(v___x_3526_)) as u8;
                        if v_isSharedCheck_3535_ == 0 {
                            v___x_3529_ = v___x_3526_;
                            v_isShared_3530_ = v_isSharedCheck_3535_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3527_);
                            leanh::lean_dec(v___x_3526_);
                            v___x_3529_ = leanh::lean_box(0);
                            v_isShared_3530_ = v_isSharedCheck_3535_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3536_ = leanh::lean_ctor_get(v___x_3526_, 0);
                        v_isSharedCheck_3543_ =
                            (!leanh::lean_is_exclusive(v___x_3526_)) as u8;
                        if v_isSharedCheck_3543_ == 0 {
                            v___x_3538_ = v___x_3526_;
                            v_isShared_3539_ = v_isSharedCheck_3543_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3536_);
                            leanh::lean_dec(v___x_3526_);
                            v___x_3538_ = leanh::lean_box(0);
                            v_isShared_3539_ = v_isSharedCheck_3543_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3531_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3531_, 0, v_a_3527_);
                if v_isShared_3530_ == 0 {
                    leanh::lean_ctor_set(v___x_3529_, 0, v___x_3531_);
                    v___x_3533_ = v___x_3529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
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
                    v_reuseFailAlloc_3542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
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
    mut v_goal_3544_: *mut leanh::LeanObject,
    mut v_target_3545_: *mut leanh::LeanObject,
    mut v_a_3546_: *mut leanh::LeanObject,
    mut v_a_3547_: *mut leanh::LeanObject,
    mut v_a_3548_: *mut leanh::LeanObject,
    mut v_a_3549_: *mut leanh::LeanObject,
    mut v_a_3550_: *mut leanh::LeanObject,
    mut v_a_3551_: *mut leanh::LeanObject,
    mut v_a_3552_: *mut leanh::LeanObject,
    mut v_a_3553_: *mut leanh::LeanObject,
    mut v_a_3554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3555_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(v_goal_3544_, v_target_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
    leanh::lean_dec(v_a_3553_);
    leanh::lean_dec_ref(v_a_3552_);
    leanh::lean_dec(v_a_3551_);
    leanh::lean_dec_ref(v_a_3550_);
    leanh::lean_dec(v_a_3549_);
    leanh::lean_dec_ref(v_a_3548_);
    leanh::lean_dec(v_a_3547_);
    leanh::lean_dec_ref(v_a_3546_);
    leanh::lean_dec_ref(v_target_3545_);
    return v_res_3555_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro(
    mut v_goal_3556_: *mut leanh::LeanObject,
    mut v_target_3557_: *mut leanh::LeanObject,
    mut v_a_3558_: *mut leanh::LeanObject,
    mut v_a_3559_: *mut leanh::LeanObject,
    mut v_a_3560_: *mut leanh::LeanObject,
    mut v_a_3561_: *mut leanh::LeanObject,
    mut v_a_3562_: *mut leanh::LeanObject,
    mut v_a_3563_: *mut leanh::LeanObject,
    mut v_a_3564_: *mut leanh::LeanObject,
    mut v_a_3565_: *mut leanh::LeanObject,
    mut v_a_3566_: *mut leanh::LeanObject,
    mut v_a_3567_: *mut leanh::LeanObject,
    mut v_a_3568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3570_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(v_goal_3556_, v_target_3557_, v_a_3558_, v_a_3559_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_);
    return v___x_3570_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___boxed(
    mut v_goal_3571_: *mut leanh::LeanObject,
    mut v_target_3572_: *mut leanh::LeanObject,
    mut v_a_3573_: *mut leanh::LeanObject,
    mut v_a_3574_: *mut leanh::LeanObject,
    mut v_a_3575_: *mut leanh::LeanObject,
    mut v_a_3576_: *mut leanh::LeanObject,
    mut v_a_3577_: *mut leanh::LeanObject,
    mut v_a_3578_: *mut leanh::LeanObject,
    mut v_a_3579_: *mut leanh::LeanObject,
    mut v_a_3580_: *mut leanh::LeanObject,
    mut v_a_3581_: *mut leanh::LeanObject,
    mut v_a_3582_: *mut leanh::LeanObject,
    mut v_a_3583_: *mut leanh::LeanObject,
    mut v_a_3584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3585_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro(v_goal_3571_, v_target_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
    leanh::lean_dec(v_a_3583_);
    leanh::lean_dec_ref(v_a_3582_);
    leanh::lean_dec(v_a_3581_);
    leanh::lean_dec_ref(v_a_3580_);
    leanh::lean_dec(v_a_3579_);
    leanh::lean_dec_ref(v_a_3578_);
    leanh::lean_dec(v_a_3577_);
    leanh::lean_dec_ref(v_a_3576_);
    leanh::lean_dec(v_a_3575_);
    leanh::lean_dec(v_a_3574_);
    leanh::lean_dec_ref(v_a_3573_);
    leanh::lean_dec_ref(v_target_3572_);
    return v_res_3585_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(
    mut v_msgData_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
    mut v___y_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = lean_st_ref_get(v___y_3590_);
    v_env_3593_ = leanh::lean_ctor_get(v___x_3592_, 0);
    leanh::lean_inc_ref(v_env_3593_);
    leanh::lean_dec(v___x_3592_);
    v___x_3594_ = lean_st_ref_get(v___y_3588_);
    v_mctx_3595_ = leanh::lean_ctor_get(v___x_3594_, 0);
    leanh::lean_inc_ref(v_mctx_3595_);
    leanh::lean_dec(v___x_3594_);
    v_lctx_3596_ = leanh::lean_ctor_get(v___y_3587_, 2);
    v_options_3597_ = leanh::lean_ctor_get(v___y_3589_, 2);
    leanh::lean_inc_ref(v_options_3597_);
    leanh::lean_inc_ref(v_lctx_3596_);
    v___x_3598_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3598_, 0, v_env_3593_);
    leanh::lean_ctor_set(v___x_3598_, 1, v_mctx_3595_);
    leanh::lean_ctor_set(v___x_3598_, 2, v_lctx_3596_);
    leanh::lean_ctor_set(v___x_3598_, 3, v_options_3597_);
    v___x_3599_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3599_, 0, v___x_3598_);
    leanh::lean_ctor_set(v___x_3599_, 1, v_msgData_3586_);
    v___x_3600_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3600_, 0, v___x_3599_);
    return v___x_3600_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0___boxed(
    mut v_msgData_3601_: *mut leanh::LeanObject,
    mut v___y_3602_: *mut leanh::LeanObject,
    mut v___y_3603_: *mut leanh::LeanObject,
    mut v___y_3604_: *mut leanh::LeanObject,
    mut v___y_3605_: *mut leanh::LeanObject,
    mut v___y_3606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3607_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msgData_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
    leanh::lean_dec(v___y_3605_);
    leanh::lean_dec_ref(v___y_3604_);
    leanh::lean_dec(v___y_3603_);
    leanh::lean_dec_ref(v___y_3602_);
    return v_res_3607_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: f64 = 0.0;
    v___x_3608_ = leanh::lean_unsigned_to_nat(0);
    v___x_3609_ = lean_float_of_nat(v___x_3608_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(
    mut v_cls_3613_: *mut leanh::LeanObject,
    mut v_msg_3614_: *mut leanh::LeanObject,
    mut v___y_3615_: *mut leanh::LeanObject,
    mut v___y_3616_: *mut leanh::LeanObject,
    mut v___y_3617_: *mut leanh::LeanObject,
    mut v___y_3618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3625_: u8 = 0;
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3638_: u8 = 0;
    let mut v_tid_3639_: u64 = 0;
    let mut v_traces_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3643_: u8 = 0;
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: f64 = 0.0;
    let mut v___x_3646_: u8 = 0;
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3664_: u8 = 0;
    let mut v_isSharedCheck_3665_: u8 = 0;
    let mut v_isSharedCheck_3666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3620_ = leanh::lean_ctor_get(v___y_3617_, 5);
                v___x_3621_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msg_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
                v_a_3622_ = leanh::lean_ctor_get(v___x_3621_, 0);
                v_isSharedCheck_3666_ = (!leanh::lean_is_exclusive(v___x_3621_)) as u8;
                if v_isSharedCheck_3666_ == 0 {
                    v___x_3624_ = v___x_3621_;
                    v_isShared_3625_ = v_isSharedCheck_3666_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3622_);
                    leanh::lean_dec(v___x_3621_);
                    v___x_3624_ = leanh::lean_box(0);
                    v_isShared_3625_ = v_isSharedCheck_3666_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3626_ = lean_st_ref_take(v___y_3618_);
                v_traceState_3627_ = leanh::lean_ctor_get(v___x_3626_, 4);
                v_env_3628_ = leanh::lean_ctor_get(v___x_3626_, 0);
                v_nextMacroScope_3629_ = leanh::lean_ctor_get(v___x_3626_, 1);
                v_ngen_3630_ = leanh::lean_ctor_get(v___x_3626_, 2);
                v_auxDeclNGen_3631_ = leanh::lean_ctor_get(v___x_3626_, 3);
                v_cache_3632_ = leanh::lean_ctor_get(v___x_3626_, 5);
                v_messages_3633_ = leanh::lean_ctor_get(v___x_3626_, 6);
                v_infoState_3634_ = leanh::lean_ctor_get(v___x_3626_, 7);
                v_snapshotTasks_3635_ = leanh::lean_ctor_get(v___x_3626_, 8);
                v_isSharedCheck_3665_ = (!leanh::lean_is_exclusive(v___x_3626_)) as u8;
                if v_isSharedCheck_3665_ == 0 {
                    v___x_3637_ = v___x_3626_;
                    v_isShared_3638_ = v_isSharedCheck_3665_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3635_);
                    leanh::lean_inc(v_infoState_3634_);
                    leanh::lean_inc(v_messages_3633_);
                    leanh::lean_inc(v_cache_3632_);
                    leanh::lean_inc(v_traceState_3627_);
                    leanh::lean_inc(v_auxDeclNGen_3631_);
                    leanh::lean_inc(v_ngen_3630_);
                    leanh::lean_inc(v_nextMacroScope_3629_);
                    leanh::lean_inc(v_env_3628_);
                    leanh::lean_dec(v___x_3626_);
                    v___x_3637_ = leanh::lean_box(0);
                    v_isShared_3638_ = v_isSharedCheck_3665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3639_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3627_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3640_ = leanh::lean_ctor_get(v_traceState_3627_, 0);
                v_isSharedCheck_3664_ =
                    (!leanh::lean_is_exclusive(v_traceState_3627_)) as u8;
                if v_isSharedCheck_3664_ == 0 {
                    v___x_3642_ = v_traceState_3627_;
                    v_isShared_3643_ = v_isSharedCheck_3664_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3640_);
                    leanh::lean_dec(v_traceState_3627_);
                    v___x_3642_ = leanh::lean_box(0);
                    v_isShared_3643_ = v_isSharedCheck_3664_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3644_ = leanh::lean_box(0);
                v___x_3645_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0);
                v___x_3646_ = 0;
                v___x_3647_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1;
                v___x_3648_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_3648_, 0, v_cls_3613_);
                leanh::lean_ctor_set(v___x_3648_, 1, v___x_3644_);
                leanh::lean_ctor_set(v___x_3648_, 2, v___x_3647_);
                leanh::lean_ctor_set_float(
                    v___x_3648_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3645_,
                );
                leanh::lean_ctor_set_float(
                    v___x_3648_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3645_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3648_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3646_,
                );
                v___x_3649_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2;
                v___x_3650_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3650_, 0, v___x_3648_);
                leanh::lean_ctor_set(v___x_3650_, 1, v_a_3622_);
                leanh::lean_ctor_set(v___x_3650_, 2, v___x_3649_);
                leanh::lean_inc(v_ref_3620_);
                v___x_3651_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3651_, 0, v_ref_3620_);
                leanh::lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                v___x_3652_ = l_Lean_PersistentArray_push___redArg(v_traces_3640_, v___x_3651_);
                if v_isShared_3643_ == 0 {
                    leanh::lean_ctor_set(v___x_3642_, 0, v___x_3652_);
                    v___x_3654_ = v___x_3642_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3652_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3663_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3639_,
                    );
                    v___x_3654_ = v_reuseFailAlloc_3663_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3638_ == 0 {
                    leanh::lean_ctor_set(v___x_3637_, 4, v___x_3654_);
                    v___x_3656_ = v___x_3637_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_env_3628_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_nextMacroScope_3629_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 2, v_ngen_3630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 3, v_auxDeclNGen_3631_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 4, v___x_3654_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 5, v_cache_3632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 6, v_messages_3633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 7, v_infoState_3634_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 8, v_snapshotTasks_3635_);
                    v___x_3656_ = v_reuseFailAlloc_3662_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3657_ = lean_st_ref_set(v___y_3618_, v___x_3656_);
                v___x_3658_ = leanh::lean_box(0);
                if v_isShared_3625_ == 0 {
                    leanh::lean_ctor_set(v___x_3624_, 0, v___x_3658_);
                    v___x_3660_ = v___x_3624_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
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
    mut v_cls_3667_: *mut leanh::LeanObject,
    mut v_msg_3668_: *mut leanh::LeanObject,
    mut v___y_3669_: *mut leanh::LeanObject,
    mut v___y_3670_: *mut leanh::LeanObject,
    mut v___y_3671_: *mut leanh::LeanObject,
    mut v___y_3672_: *mut leanh::LeanObject,
    mut v___y_3673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3674_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_3667_, v_msg_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
    leanh::lean_dec(v___y_3672_);
    leanh::lean_dec_ref(v___y_3671_);
    leanh::lean_dec(v___y_3670_);
    leanh::lean_dec_ref(v___y_3669_);
    return v_res_3674_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(
    mut v_msg_3675_: *mut leanh::LeanObject,
    mut v___y_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3681_ = leanh::lean_ctor_get(v___y_3678_, 5);
                v___x_3682_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msg_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
                v_a_3683_ = leanh::lean_ctor_get(v___x_3682_, 0);
                v_isSharedCheck_3691_ = (!leanh::lean_is_exclusive(v___x_3682_)) as u8;
                if v_isSharedCheck_3691_ == 0 {
                    v___x_3685_ = v___x_3682_;
                    v_isShared_3686_ = v_isSharedCheck_3691_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3683_);
                    leanh::lean_dec(v___x_3682_);
                    v___x_3685_ = leanh::lean_box(0);
                    v_isShared_3686_ = v_isSharedCheck_3691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3681_);
                v___x_3687_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3687_, 0, v_ref_3681_);
                leanh::lean_ctor_set(v___x_3687_, 1, v_a_3683_);
                if v_isShared_3686_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3685_, 1);
                    leanh::lean_ctor_set(v___x_3685_, 0, v___x_3687_);
                    v___x_3689_ = v___x_3685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
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
    mut v_msg_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
    mut v___y_3694_: *mut leanh::LeanObject,
    mut v___y_3695_: *mut leanh::LeanObject,
    mut v___y_3696_: *mut leanh::LeanObject,
    mut v___y_3697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3698_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v_msg_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
    leanh::lean_dec(v___y_3696_);
    leanh::lean_dec_ref(v___y_3695_);
    leanh::lean_dec(v___y_3694_);
    leanh::lean_dec_ref(v___y_3693_);
    return v_res_3698_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0;
    v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
    v___x_3715_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8;
    v___x_3716_ = l_Lean_Name_append(v___x_3715_, v___x_3714_);
    return v___x_3716_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3718_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10;
    v___x_3719_ = l_Lean_stringToMessageData(v___x_3718_);
    return v___x_3719_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12;
    v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
    return v___x_3722_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3724_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14;
    v___x_3725_ = l_Lean_stringToMessageData(v___x_3724_);
    return v___x_3725_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(
    mut v_goal_3726_: *mut leanh::LeanObject,
    mut v_target_3727_: *mut leanh::LeanObject,
    mut v_a_3728_: *mut leanh::LeanObject,
    mut v_a_3729_: *mut leanh::LeanObject,
    mut v_a_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
    mut v_a_3732_: *mut leanh::LeanObject,
    mut v_a_3733_: *mut leanh::LeanObject,
    mut v_a_3734_: *mut leanh::LeanObject,
    mut v_a_3735_: *mut leanh::LeanObject,
    mut v_a_3736_: *mut leanh::LeanObject,
    mut v_a_3737_: *mut leanh::LeanObject,
    mut v_a_3738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3762_: u8 = 0;
    let mut v_a_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v___y_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3788_: u8 = 0;
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut v_a_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3801_: u8 = 0;
    let mut v_a_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3805_: u8 = 0;
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut v___y_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: u8 = 0;
    let mut v_options_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3825_: u8 = 0;
    let mut v_inheritedTraceOptions_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3838_: u8 = 0;
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v_options_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3844_: u8 = 0;
    let mut v_inheritedTraceOptions_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut v___x_3862_: u8 = 0;
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_useJP_3865_: u8 = 0;
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3862_ = l_Lean_Expr_isLet(v_target_3727_);
                if v___x_3862_ == 0 {
                    leanh::lean_dec(v_goal_3726_);
                    v___x_3863_ = leanh::lean_box(0);
                    v___x_3864_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3864_, 0, v___x_3863_);
                    return v___x_3864_;
                } else {
                    v_useJP_3865_ = leanh::lean_ctor_get_uint8(
                        v_a_3728_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 19 + 1) as u32,
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
                        leanh::lean_inc(v___x_3866_);
                        v___x_3867_ = l_Lean_Elab_Tactic_Do_isJP(v___x_3866_);
                        if v___x_3867_ == 0 {
                            leanh::lean_dec(v___x_3866_);
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
                            leanh::lean_dec_ref(v___x_3868_);
                            if v___x_3869_ == 0 {
                                leanh::lean_dec(v___x_3866_);
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
                                leanh::lean_dec(v_goal_3726_);
                                v___x_3870_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13);
                                v___x_3871_ = l_Lean_MessageData_ofName(v___x_3866_);
                                v___x_3872_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3872_, 0, v___x_3870_);
                                leanh::lean_ctor_set(v___x_3872_, 1, v___x_3871_);
                                v___x_3873_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15);
                                v___x_3874_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3874_, 0, v___x_3872_);
                                leanh::lean_ctor_set(v___x_3874_, 1, v___x_3873_);
                                v___x_3875_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_3874_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
                                v_a_3876_ = leanh::lean_ctor_get(v___x_3875_, 0);
                                v_isSharedCheck_3883_ =
                                    (!leanh::lean_is_exclusive(v___x_3875_)) as u8;
                                if v_isSharedCheck_3883_ == 0 {
                                    v___x_3878_ = v___x_3875_;
                                    v_isShared_3879_ = v_isSharedCheck_3883_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3876_);
                                    leanh::lean_dec(v___x_3875_);
                                    v___x_3878_ = leanh::lean_box(0);
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
                v___x_3749_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1);
                v___x_3750_ = l_Lean_Expr_letName_x21(v_target_3727_);
                v___x_3751_ = l_Lean_MessageData_ofName(v___x_3750_);
                v___x_3752_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3752_, 0, v___x_3749_);
                leanh::lean_ctor_set(v___x_3752_, 1, v___x_3751_);
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
                if leanh::lean_obj_tag(v___x_3753_) == 0 {
                    v_a_3754_ = leanh::lean_ctor_get(v___x_3753_, 0);
                    v_isSharedCheck_3762_ = (!leanh::lean_is_exclusive(v___x_3753_)) as u8;
                    if v_isSharedCheck_3762_ == 0 {
                        v___x_3756_ = v___x_3753_;
                        v_isShared_3757_ = v_isSharedCheck_3762_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3754_);
                        leanh::lean_dec(v___x_3753_);
                        v___x_3756_ = leanh::lean_box(0);
                        v_isShared_3757_ = v_isSharedCheck_3762_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3763_ = leanh::lean_ctor_get(v___x_3753_, 0);
                    v_isSharedCheck_3770_ = (!leanh::lean_is_exclusive(v___x_3753_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3765_ = v___x_3753_;
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3763_);
                        leanh::lean_dec(v___x_3753_);
                        v___x_3765_ = leanh::lean_box(0);
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3758_, 0, v_a_3754_);
                if v_isShared_3757_ == 0 {
                    leanh::lean_ctor_set(v___x_3756_, 0, v___x_3758_);
                    v___x_3760_ = v___x_3756_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3761_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
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
                    v_reuseFailAlloc_3769_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
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
                v___x_3779_ = leanh::lean_unsigned_to_nat(1);
                v___x_3780_ = lean_mk_empty_array_with_capacity(v___x_3779_);
                v___x_3781_ = lean_array_push(v___x_3780_, v___y_3772_);
                v___x_3782_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                    v___x_3778_,
                    v___x_3781_,
                    v___y_3773_,
                );
                leanh::lean_dec_ref(v___x_3781_);
                if leanh::lean_obj_tag(v___x_3782_) == 0 {
                    v_a_3783_ = leanh::lean_ctor_get(v___x_3782_, 0);
                    leanh::lean_inc(v_a_3783_);
                    leanh::lean_dec_ref_known(v___x_3782_, 1);
                    v___x_3784_ = l_Lean_MVarId_replaceTargetDefEq(
                        v_goal_3726_,
                        v_a_3783_,
                        v___y_3774_,
                        v___y_3775_,
                        v___y_3776_,
                        v___y_3777_,
                    );
                    if leanh::lean_obj_tag(v___x_3784_) == 0 {
                        v_a_3785_ = leanh::lean_ctor_get(v___x_3784_, 0);
                        v_isSharedCheck_3793_ =
                            (!leanh::lean_is_exclusive(v___x_3784_)) as u8;
                        if v_isSharedCheck_3793_ == 0 {
                            v___x_3787_ = v___x_3784_;
                            v_isShared_3788_ = v_isSharedCheck_3793_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3785_);
                            leanh::lean_dec(v___x_3784_);
                            v___x_3787_ = leanh::lean_box(0);
                            v_isShared_3788_ = v_isSharedCheck_3793_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_a_3794_ = leanh::lean_ctor_get(v___x_3784_, 0);
                        v_isSharedCheck_3801_ =
                            (!leanh::lean_is_exclusive(v___x_3784_)) as u8;
                        if v_isSharedCheck_3801_ == 0 {
                            v___x_3796_ = v___x_3784_;
                            v_isShared_3797_ = v_isSharedCheck_3801_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3794_);
                            leanh::lean_dec(v___x_3784_);
                            v___x_3796_ = leanh::lean_box(0);
                            v_isShared_3797_ = v_isSharedCheck_3801_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_goal_3726_);
                    v_a_3802_ = leanh::lean_ctor_get(v___x_3782_, 0);
                    v_isSharedCheck_3809_ = (!leanh::lean_is_exclusive(v___x_3782_)) as u8;
                    if v_isSharedCheck_3809_ == 0 {
                        v___x_3804_ = v___x_3782_;
                        v_isShared_3805_ = v_isSharedCheck_3809_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3802_);
                        leanh::lean_dec(v___x_3782_);
                        v___x_3804_ = leanh::lean_box(0);
                        v_isShared_3805_ = v_isSharedCheck_3809_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3789_, 0, v_a_3785_);
                if v_isShared_3788_ == 0 {
                    leanh::lean_ctor_set(v___x_3787_, 0, v___x_3789_);
                    v___x_3791_ = v___x_3787_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3792_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
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
                    v_reuseFailAlloc_3800_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
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
                    v_reuseFailAlloc_3808_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
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
                    leanh::lean_dec_ref(v___x_3822_);
                    v_options_3824_ = leanh::lean_ctor_get(v___y_3820_, 2);
                    v_hasTrace_3825_ = leanh::lean_ctor_get_uint8(
                        v_options_3824_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                            leanh::lean_ctor_get(v___y_3820_, 13);
                        v___x_3827_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                        v___x_3828_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
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
                            v___x_3830_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1);
                            v___x_3831_ = l_Lean_Expr_letName_x21(v_target_3727_);
                            v___x_3832_ = l_Lean_MessageData_ofName(v___x_3831_);
                            v___x_3833_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3833_, 0, v___x_3830_);
                            leanh::lean_ctor_set(v___x_3833_, 1, v___x_3832_);
                            v___x_3834_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_3827_, v___x_3833_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
                            if leanh::lean_obj_tag(v___x_3834_) == 0 {
                                leanh::lean_dec_ref_known(v___x_3834_, 1);
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
                                leanh::lean_dec(v_goal_3726_);
                                v_a_3835_ = leanh::lean_ctor_get(v___x_3834_, 0);
                                v_isSharedCheck_3842_ =
                                    (!leanh::lean_is_exclusive(v___x_3834_)) as u8;
                                if v_isSharedCheck_3842_ == 0 {
                                    v___x_3837_ = v___x_3834_;
                                    v_isShared_3838_ = v_isSharedCheck_3842_;
                                    state = 14;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3835_);
                                    leanh::lean_dec(v___x_3834_);
                                    v___x_3837_ = leanh::lean_box(0);
                                    v_isShared_3838_ = v_isSharedCheck_3842_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v_options_3843_ = leanh::lean_ctor_get(v___y_3820_, 2);
                    v_hasTrace_3844_ = leanh::lean_ctor_get_uint8(
                        v_options_3843_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                            leanh::lean_ctor_get(v___y_3820_, 13);
                        v___x_3846_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                        v___x_3847_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
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
                            v___x_3849_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11);
                            v___x_3850_ = l_Lean_Expr_letName_x21(v_target_3727_);
                            v___x_3851_ = l_Lean_MessageData_ofName(v___x_3850_);
                            v___x_3852_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3852_, 0, v___x_3849_);
                            leanh::lean_ctor_set(v___x_3852_, 1, v___x_3851_);
                            v___x_3853_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_3846_, v___x_3852_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
                            if leanh::lean_obj_tag(v___x_3853_) == 0 {
                                leanh::lean_dec_ref_known(v___x_3853_, 1);
                                v___y_3772_ = v___x_3822_;
                                v___y_3773_ = v___y_3817_;
                                v___y_3774_ = v___y_3818_;
                                v___y_3775_ = v___y_3819_;
                                v___y_3776_ = v___y_3820_;
                                v___y_3777_ = v___y_3821_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___x_3822_);
                                leanh::lean_dec(v_goal_3726_);
                                v_a_3854_ = leanh::lean_ctor_get(v___x_3853_, 0);
                                v_isSharedCheck_3861_ =
                                    (!leanh::lean_is_exclusive(v___x_3853_)) as u8;
                                if v_isSharedCheck_3861_ == 0 {
                                    v___x_3856_ = v___x_3853_;
                                    v_isShared_3857_ = v_isSharedCheck_3861_;
                                    state = 16;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3854_);
                                    leanh::lean_dec(v___x_3853_);
                                    v___x_3856_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3841_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
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
                    v_reuseFailAlloc_3860_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
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
                    v_reuseFailAlloc_3882_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
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
    mut v_goal_3884_: *mut leanh::LeanObject,
    mut v_target_3885_: *mut leanh::LeanObject,
    mut v_a_3886_: *mut leanh::LeanObject,
    mut v_a_3887_: *mut leanh::LeanObject,
    mut v_a_3888_: *mut leanh::LeanObject,
    mut v_a_3889_: *mut leanh::LeanObject,
    mut v_a_3890_: *mut leanh::LeanObject,
    mut v_a_3891_: *mut leanh::LeanObject,
    mut v_a_3892_: *mut leanh::LeanObject,
    mut v_a_3893_: *mut leanh::LeanObject,
    mut v_a_3894_: *mut leanh::LeanObject,
    mut v_a_3895_: *mut leanh::LeanObject,
    mut v_a_3896_: *mut leanh::LeanObject,
    mut v_a_3897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3898_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(v_goal_3884_, v_target_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
    leanh::lean_dec(v_a_3896_);
    leanh::lean_dec_ref(v_a_3895_);
    leanh::lean_dec(v_a_3894_);
    leanh::lean_dec_ref(v_a_3893_);
    leanh::lean_dec(v_a_3892_);
    leanh::lean_dec_ref(v_a_3891_);
    leanh::lean_dec(v_a_3890_);
    leanh::lean_dec_ref(v_a_3889_);
    leanh::lean_dec(v_a_3888_);
    leanh::lean_dec(v_a_3887_);
    leanh::lean_dec_ref(v_a_3886_);
    leanh::lean_dec_ref(v_target_3885_);
    return v_res_3898_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0(
    mut v_cls_3899_: *mut leanh::LeanObject,
    mut v_msg_3900_: *mut leanh::LeanObject,
    mut v___y_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
    mut v___y_3903_: *mut leanh::LeanObject,
    mut v___y_3904_: *mut leanh::LeanObject,
    mut v___y_3905_: *mut leanh::LeanObject,
    mut v___y_3906_: *mut leanh::LeanObject,
    mut v___y_3907_: *mut leanh::LeanObject,
    mut v___y_3908_: *mut leanh::LeanObject,
    mut v___y_3909_: *mut leanh::LeanObject,
    mut v___y_3910_: *mut leanh::LeanObject,
    mut v___y_3911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3913_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_3899_, v_msg_3900_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
    return v___x_3913_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___boxed(
    mut v_cls_3914_: *mut leanh::LeanObject,
    mut v_msg_3915_: *mut leanh::LeanObject,
    mut v___y_3916_: *mut leanh::LeanObject,
    mut v___y_3917_: *mut leanh::LeanObject,
    mut v___y_3918_: *mut leanh::LeanObject,
    mut v___y_3919_: *mut leanh::LeanObject,
    mut v___y_3920_: *mut leanh::LeanObject,
    mut v___y_3921_: *mut leanh::LeanObject,
    mut v___y_3922_: *mut leanh::LeanObject,
    mut v___y_3923_: *mut leanh::LeanObject,
    mut v___y_3924_: *mut leanh::LeanObject,
    mut v___y_3925_: *mut leanh::LeanObject,
    mut v___y_3926_: *mut leanh::LeanObject,
    mut v___y_3927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3928_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0(v_cls_3914_, v_msg_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
    leanh::lean_dec(v___y_3926_);
    leanh::lean_dec_ref(v___y_3925_);
    leanh::lean_dec(v___y_3924_);
    leanh::lean_dec_ref(v___y_3923_);
    leanh::lean_dec(v___y_3922_);
    leanh::lean_dec_ref(v___y_3921_);
    leanh::lean_dec(v___y_3920_);
    leanh::lean_dec_ref(v___y_3919_);
    leanh::lean_dec(v___y_3918_);
    leanh::lean_dec(v___y_3917_);
    leanh::lean_dec_ref(v___y_3916_);
    return v_res_3928_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1(
    mut v_00_u03b1_3929_: *mut leanh::LeanObject,
    mut v_msg_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
    mut v___y_3935_: *mut leanh::LeanObject,
    mut v___y_3936_: *mut leanh::LeanObject,
    mut v___y_3937_: *mut leanh::LeanObject,
    mut v___y_3938_: *mut leanh::LeanObject,
    mut v___y_3939_: *mut leanh::LeanObject,
    mut v___y_3940_: *mut leanh::LeanObject,
    mut v___y_3941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v_msg_3930_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
    return v___x_3943_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___boxed(
    mut v_00_u03b1_3944_: *mut leanh::LeanObject,
    mut v_msg_3945_: *mut leanh::LeanObject,
    mut v___y_3946_: *mut leanh::LeanObject,
    mut v___y_3947_: *mut leanh::LeanObject,
    mut v___y_3948_: *mut leanh::LeanObject,
    mut v___y_3949_: *mut leanh::LeanObject,
    mut v___y_3950_: *mut leanh::LeanObject,
    mut v___y_3951_: *mut leanh::LeanObject,
    mut v___y_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
    mut v___y_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
    mut v___y_3956_: *mut leanh::LeanObject,
    mut v___y_3957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3958_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1(v_00_u03b1_3944_, v_msg_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
    leanh::lean_dec(v___y_3956_);
    leanh::lean_dec_ref(v___y_3955_);
    leanh::lean_dec(v___y_3954_);
    leanh::lean_dec_ref(v___y_3953_);
    leanh::lean_dec(v___y_3952_);
    leanh::lean_dec_ref(v___y_3951_);
    leanh::lean_dec(v___y_3950_);
    leanh::lean_dec_ref(v___y_3949_);
    leanh::lean_dec(v___y_3948_);
    leanh::lean_dec(v___y_3947_);
    leanh::lean_dec_ref(v___y_3946_);
    return v_res_3958_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(
    mut v_goal_3965_: *mut leanh::LeanObject,
    mut v_target_3966_: *mut leanh::LeanObject,
    mut v_a_3967_: *mut leanh::LeanObject,
    mut v_a_3968_: *mut leanh::LeanObject,
    mut v_a_3969_: *mut leanh::LeanObject,
    mut v_a_3970_: *mut leanh::LeanObject,
    mut v_a_3971_: *mut leanh::LeanObject,
    mut v_a_3972_: *mut leanh::LeanObject,
    mut v_a_3973_: *mut leanh::LeanObject,
    mut v_a_3974_: *mut leanh::LeanObject,
    mut v_a_3975_: *mut leanh::LeanObject,
    mut v_a_3976_: *mut leanh::LeanObject,
    mut v_a_3977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: u8 = 0;
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3988_: u8 = 0;
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3993_: u8 = 0;
    let mut v_a_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3997_: u8 = 0;
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3979_ = l_Lean_Expr_getAppFn(v_target_3966_);
                v___x_3980_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2;
                v___x_3981_ = l_Lean_Expr_isConstOf(v___x_3979_, v___x_3980_);
                leanh::lean_dec_ref(v___x_3979_);
                if v___x_3981_ == 0 {
                    leanh::lean_dec(v_goal_3965_);
                    v___x_3982_ = leanh::lean_box(0);
                    v___x_3983_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3983_, 0, v___x_3982_);
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
                    if leanh::lean_obj_tag(v___x_3984_) == 0 {
                        v_a_3985_ = leanh::lean_ctor_get(v___x_3984_, 0);
                        v_isSharedCheck_3993_ =
                            (!leanh::lean_is_exclusive(v___x_3984_)) as u8;
                        if v_isSharedCheck_3993_ == 0 {
                            v___x_3987_ = v___x_3984_;
                            v_isShared_3988_ = v_isSharedCheck_3993_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3985_);
                            leanh::lean_dec(v___x_3984_);
                            v___x_3987_ = leanh::lean_box(0);
                            v_isShared_3988_ = v_isSharedCheck_3993_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3994_ = leanh::lean_ctor_get(v___x_3984_, 0);
                        v_isSharedCheck_4001_ =
                            (!leanh::lean_is_exclusive(v___x_3984_)) as u8;
                        if v_isSharedCheck_4001_ == 0 {
                            v___x_3996_ = v___x_3984_;
                            v_isShared_3997_ = v_isSharedCheck_4001_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3994_);
                            leanh::lean_dec(v___x_3984_);
                            v___x_3996_ = leanh::lean_box(0);
                            v_isShared_3997_ = v_isSharedCheck_4001_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3989_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3989_, 0, v_a_3985_);
                if v_isShared_3988_ == 0 {
                    leanh::lean_ctor_set(v___x_3987_, 0, v___x_3989_);
                    v___x_3991_ = v___x_3987_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3992_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3989_);
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
                    v_reuseFailAlloc_4000_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
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
    mut v_goal_4002_: *mut leanh::LeanObject,
    mut v_target_4003_: *mut leanh::LeanObject,
    mut v_a_4004_: *mut leanh::LeanObject,
    mut v_a_4005_: *mut leanh::LeanObject,
    mut v_a_4006_: *mut leanh::LeanObject,
    mut v_a_4007_: *mut leanh::LeanObject,
    mut v_a_4008_: *mut leanh::LeanObject,
    mut v_a_4009_: *mut leanh::LeanObject,
    mut v_a_4010_: *mut leanh::LeanObject,
    mut v_a_4011_: *mut leanh::LeanObject,
    mut v_a_4012_: *mut leanh::LeanObject,
    mut v_a_4013_: *mut leanh::LeanObject,
    mut v_a_4014_: *mut leanh::LeanObject,
    mut v_a_4015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4016_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(v_goal_4002_, v_target_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
    leanh::lean_dec(v_a_4014_);
    leanh::lean_dec_ref(v_a_4013_);
    leanh::lean_dec(v_a_4012_);
    leanh::lean_dec_ref(v_a_4011_);
    leanh::lean_dec(v_a_4010_);
    leanh::lean_dec_ref(v_a_4009_);
    leanh::lean_dec(v_a_4008_);
    leanh::lean_dec_ref(v_a_4007_);
    leanh::lean_dec(v_a_4006_);
    leanh::lean_dec(v_a_4005_);
    leanh::lean_dec_ref(v_a_4004_);
    leanh::lean_dec_ref(v_target_4003_);
    return v_res_4016_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4018_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0;
    v___x_4019_ = l_Lean_stringToMessageData(v___x_4018_);
    return v___x_4019_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4027_: u8 = 0;
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4027_ = 0;
    v___x_4028_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4;
    v___x_4029_ = l_Lean_MessageData_ofConstName(v___x_4028_, v___x_4027_);
    return v___x_4029_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4030_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5);
    v___x_4031_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1);
    v___x_4032_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4032_, 0, v___x_4031_);
    leanh::lean_ctor_set(v___x_4032_, 1, v___x_4030_);
    return v___x_4032_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4034_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7;
    v___x_4035_ = l_Lean_stringToMessageData(v___x_4034_);
    return v___x_4035_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4036_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8);
    v___x_4037_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6);
    v___x_4038_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4038_, 0, v___x_4037_);
    leanh::lean_ctor_set(v___x_4038_, 1, v___x_4036_);
    return v___x_4038_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4040_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10;
    v___x_4041_ = l_Lean_stringToMessageData(v___x_4040_);
    return v___x_4041_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(
    mut v_goal_4042_: *mut leanh::LeanObject,
    mut v_T_4043_: *mut leanh::LeanObject,
    mut v_a_4044_: *mut leanh::LeanObject,
    mut v_a_4045_: *mut leanh::LeanObject,
    mut v_a_4046_: *mut leanh::LeanObject,
    mut v_a_4047_: *mut leanh::LeanObject,
    mut v_a_4048_: *mut leanh::LeanObject,
    mut v_a_4049_: *mut leanh::LeanObject,
    mut v_a_4050_: *mut leanh::LeanObject,
    mut v_a_4051_: *mut leanh::LeanObject,
    mut v_a_4052_: *mut leanh::LeanObject,
    mut v_a_4053_: *mut leanh::LeanObject,
    mut v_a_4054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4056_: u8 = 0;
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entailsConsIntroRule_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4065_: u8 = 0;
    let mut v___y_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4082_: u8 = 0;
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v_mvarIds_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4090_: u8 = 0;
    let mut v_tail_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut v_isSharedCheck_4100_: u8 = 0;
    let mut v_a_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4056_ = l_Lean_Expr_isLambda(v_T_4043_);
                if v___x_4056_ == 0 {
                    leanh::lean_dec(v_goal_4042_);
                    v___x_4057_ = leanh::lean_box(0);
                    v___x_4058_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4058_, 0, v___x_4057_);
                    return v___x_4058_;
                } else {
                    v_entailsConsIntroRule_4059_ = leanh::lean_ctor_get(v_a_4044_, 0);
                    v___x_4060_ = leanh::lean_box(0);
                    leanh::lean_inc(v_goal_4042_);
                    leanh::lean_inc_ref(v_entailsConsIntroRule_4059_);
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
                    if leanh::lean_obj_tag(v___x_4061_) == 0 {
                        v_a_4062_ = leanh::lean_ctor_get(v___x_4061_, 0);
                        v_isSharedCheck_4100_ =
                            (!leanh::lean_is_exclusive(v___x_4061_)) as u8;
                        if v_isSharedCheck_4100_ == 0 {
                            v___x_4064_ = v___x_4061_;
                            v_isShared_4065_ = v_isSharedCheck_4100_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4062_);
                            leanh::lean_dec(v___x_4061_);
                            v___x_4064_ = leanh::lean_box(0);
                            v_isShared_4065_ = v_isSharedCheck_4100_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_goal_4042_);
                        v_a_4101_ = leanh::lean_ctor_get(v___x_4061_, 0);
                        v_isSharedCheck_4108_ =
                            (!leanh::lean_is_exclusive(v___x_4061_)) as u8;
                        if v_isSharedCheck_4108_ == 0 {
                            v___x_4103_ = v___x_4061_;
                            v_isShared_4104_ = v_isSharedCheck_4108_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4101_);
                            leanh::lean_dec(v___x_4061_);
                            v___x_4103_ = leanh::lean_box(0);
                            v_isShared_4104_ = v_isSharedCheck_4108_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4062_) == 1 {
                    v_mvarIds_4087_ = leanh::lean_ctor_get(v_a_4062_, 0);
                    v_isSharedCheck_4099_ = (!leanh::lean_is_exclusive(v_a_4062_)) as u8;
                    if v_isSharedCheck_4099_ == 0 {
                        v___x_4089_ = v_a_4062_;
                        v_isShared_4090_ = v_isSharedCheck_4099_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_mvarIds_4087_);
                        leanh::lean_dec(v_a_4062_);
                        v___x_4089_ = leanh::lean_box(0);
                        v_isShared_4090_ = v_isSharedCheck_4099_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4064_);
                    leanh::lean_dec(v_a_4062_);
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
                if leanh::lean_obj_tag(v___x_4071_) == 0 {
                    v_a_4072_ = leanh::lean_ctor_get(v___x_4071_, 0);
                    leanh::lean_inc(v_a_4072_);
                    leanh::lean_dec_ref_known(v___x_4071_, 1);
                    v___x_4073_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9);
                    v___x_4074_ = l_Lean_MessageData_ofExpr(v_a_4072_);
                    v___x_4075_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4075_, 0, v___x_4073_);
                    leanh::lean_ctor_set(v___x_4075_, 1, v___x_4074_);
                    v___x_4076_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11);
                    v___x_4077_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4077_, 0, v___x_4075_);
                    leanh::lean_ctor_set(v___x_4077_, 1, v___x_4076_);
                    v___x_4078_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_4077_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
                    return v___x_4078_;
                } else {
                    v_a_4079_ = leanh::lean_ctor_get(v___x_4071_, 0);
                    v_isSharedCheck_4086_ = (!leanh::lean_is_exclusive(v___x_4071_)) as u8;
                    if v_isSharedCheck_4086_ == 0 {
                        v___x_4081_ = v___x_4071_;
                        v_isShared_4082_ = v_isSharedCheck_4086_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4079_);
                        leanh::lean_dec(v___x_4071_);
                        v___x_4081_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4085_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
                    v___x_4084_ = v_reuseFailAlloc_4085_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4084_;
            }
            5 => {
                if leanh::lean_obj_tag(v_mvarIds_4087_) == 1 {
                    v_tail_4091_ = leanh::lean_ctor_get(v_mvarIds_4087_, 1);
                    if leanh::lean_obj_tag(v_tail_4091_) == 0 {
                        leanh::lean_dec(v_goal_4042_);
                        v_head_4092_ = leanh::lean_ctor_get(v_mvarIds_4087_, 0);
                        leanh::lean_inc(v_head_4092_);
                        leanh::lean_dec_ref_known(v_mvarIds_4087_, 2);
                        if v_isShared_4090_ == 0 {
                            leanh::lean_ctor_set(v___x_4089_, 0, v_head_4092_);
                            v___x_4094_ = v___x_4089_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4098_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_head_4092_);
                            v___x_4094_ = v_reuseFailAlloc_4098_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_mvarIds_4087_, 2);
                        leanh::lean_del_object(v___x_4089_);
                        leanh::lean_del_object(v___x_4064_);
                        v___y_4067_ = v_a_4051_;
                        v___y_4068_ = v_a_4052_;
                        v___y_4069_ = v_a_4053_;
                        v___y_4070_ = v_a_4054_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4089_);
                    leanh::lean_dec(v_mvarIds_4087_);
                    leanh::lean_del_object(v___x_4064_);
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
                    leanh::lean_ctor_set(v___x_4064_, 0, v___x_4094_);
                    v___x_4096_ = v___x_4064_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4097_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4094_);
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
                    v_reuseFailAlloc_4107_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
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
    mut v_goal_4109_: *mut leanh::LeanObject,
    mut v_T_4110_: *mut leanh::LeanObject,
    mut v_a_4111_: *mut leanh::LeanObject,
    mut v_a_4112_: *mut leanh::LeanObject,
    mut v_a_4113_: *mut leanh::LeanObject,
    mut v_a_4114_: *mut leanh::LeanObject,
    mut v_a_4115_: *mut leanh::LeanObject,
    mut v_a_4116_: *mut leanh::LeanObject,
    mut v_a_4117_: *mut leanh::LeanObject,
    mut v_a_4118_: *mut leanh::LeanObject,
    mut v_a_4119_: *mut leanh::LeanObject,
    mut v_a_4120_: *mut leanh::LeanObject,
    mut v_a_4121_: *mut leanh::LeanObject,
    mut v_a_4122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4123_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(v_goal_4109_, v_T_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
    leanh::lean_dec(v_a_4121_);
    leanh::lean_dec_ref(v_a_4120_);
    leanh::lean_dec(v_a_4119_);
    leanh::lean_dec_ref(v_a_4118_);
    leanh::lean_dec(v_a_4117_);
    leanh::lean_dec_ref(v_a_4116_);
    leanh::lean_dec(v_a_4115_);
    leanh::lean_dec_ref(v_a_4114_);
    leanh::lean_dec(v_a_4113_);
    leanh::lean_dec(v_a_4112_);
    leanh::lean_dec_ref(v_a_4111_);
    leanh::lean_dec_ref(v_T_4110_);
    return v_res_4123_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(
    mut v_f_4124_: *mut leanh::LeanObject,
    mut v_a_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
    mut v___y_4127_: *mut leanh::LeanObject,
    mut v___y_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
    mut v___y_4130_: *mut leanh::LeanObject,
    mut v___y_4131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4138_: u8 = 0;
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4137_ = lean_st_ref_get(v___y_4127_);
                v_debug_4138_ = leanh::lean_ctor_get_uint8(
                    v___x_4137_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                leanh::lean_dec(v___x_4137_);
                if v_debug_4138_ == 0 {
                    v___y_4134_ = v___y_4127_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_f_4124_);
                    v___x_4139_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_4124_,
                        v___y_4126_,
                        v___y_4127_,
                        v___y_4128_,
                        v___y_4129_,
                        v___y_4130_,
                        v___y_4131_,
                    );
                    if leanh::lean_obj_tag(v___x_4139_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4139_, 1);
                        leanh::lean_inc_ref(v_a_4125_);
                        v___x_4140_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_4125_,
                            v___y_4126_,
                            v___y_4127_,
                            v___y_4128_,
                            v___y_4129_,
                            v___y_4130_,
                            v___y_4131_,
                        );
                        if leanh::lean_obj_tag(v___x_4140_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4140_, 1);
                            v___y_4134_ = v___y_4127_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_a_4125_);
                            leanh::lean_dec_ref(v_f_4124_);
                            v_a_4141_ = leanh::lean_ctor_get(v___x_4140_, 0);
                            v_isSharedCheck_4148_ =
                                (!leanh::lean_is_exclusive(v___x_4140_)) as u8;
                            if v_isSharedCheck_4148_ == 0 {
                                v___x_4143_ = v___x_4140_;
                                v_isShared_4144_ = v_isSharedCheck_4148_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4141_);
                                leanh::lean_dec(v___x_4140_);
                                v___x_4143_ = leanh::lean_box(0);
                                v_isShared_4144_ = v_isSharedCheck_4148_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_4125_);
                        leanh::lean_dec_ref(v_f_4124_);
                        v_a_4149_ = leanh::lean_ctor_get(v___x_4139_, 0);
                        v_isSharedCheck_4156_ =
                            (!leanh::lean_is_exclusive(v___x_4139_)) as u8;
                        if v_isSharedCheck_4156_ == 0 {
                            v___x_4151_ = v___x_4139_;
                            v_isShared_4152_ = v_isSharedCheck_4156_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4149_);
                            leanh::lean_dec(v___x_4139_);
                            v___x_4151_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4147_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
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
                    v_reuseFailAlloc_4155_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
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
    mut v_f_4157_: *mut leanh::LeanObject,
    mut v_a_4158_: *mut leanh::LeanObject,
    mut v___y_4159_: *mut leanh::LeanObject,
    mut v___y_4160_: *mut leanh::LeanObject,
    mut v___y_4161_: *mut leanh::LeanObject,
    mut v___y_4162_: *mut leanh::LeanObject,
    mut v___y_4163_: *mut leanh::LeanObject,
    mut v___y_4164_: *mut leanh::LeanObject,
    mut v___y_4165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4166_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_4157_, v_a_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
    leanh::lean_dec(v___y_4164_);
    leanh::lean_dec_ref(v___y_4163_);
    leanh::lean_dec(v___y_4162_);
    leanh::lean_dec_ref(v___y_4161_);
    leanh::lean_dec(v___y_4160_);
    leanh::lean_dec_ref(v___y_4159_);
    return v_res_4166_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(
    mut v_f_4167_: *mut leanh::LeanObject,
    mut v_a_u2081_4168_: *mut leanh::LeanObject,
    mut v_a_u2082_4169_: *mut leanh::LeanObject,
    mut v___y_4170_: *mut leanh::LeanObject,
    mut v___y_4171_: *mut leanh::LeanObject,
    mut v___y_4172_: *mut leanh::LeanObject,
    mut v___y_4173_: *mut leanh::LeanObject,
    mut v___y_4174_: *mut leanh::LeanObject,
    mut v___y_4175_: *mut leanh::LeanObject,
    mut v___y_4176_: *mut leanh::LeanObject,
    mut v___y_4177_: *mut leanh::LeanObject,
    mut v___y_4178_: *mut leanh::LeanObject,
    mut v___y_4179_: *mut leanh::LeanObject,
    mut v___y_4180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4182_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_4167_, v_a_u2081_4168_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
    if leanh::lean_obj_tag(v___x_4182_) == 0 {
        let mut v_a_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4183_ = leanh::lean_ctor_get(v___x_4182_, 0);
        leanh::lean_inc(v_a_4183_);
        leanh::lean_dec_ref_known(v___x_4182_, 1);
        v___x_4184_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_4183_, v_a_u2082_4169_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
        return v___x_4184_;
    } else {
        leanh::lean_dec_ref(v_a_u2082_4169_);
        return v___x_4182_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0___boxed(
    mut v_f_4185_: *mut leanh::LeanObject,
    mut v_a_u2081_4186_: *mut leanh::LeanObject,
    mut v_a_u2082_4187_: *mut leanh::LeanObject,
    mut v___y_4188_: *mut leanh::LeanObject,
    mut v___y_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
    mut v___y_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
    mut v___y_4193_: *mut leanh::LeanObject,
    mut v___y_4194_: *mut leanh::LeanObject,
    mut v___y_4195_: *mut leanh::LeanObject,
    mut v___y_4196_: *mut leanh::LeanObject,
    mut v___y_4197_: *mut leanh::LeanObject,
    mut v___y_4198_: *mut leanh::LeanObject,
    mut v___y_4199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4200_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(v_f_4185_, v_a_u2081_4186_, v_a_u2082_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
    leanh::lean_dec(v___y_4198_);
    leanh::lean_dec_ref(v___y_4197_);
    leanh::lean_dec(v___y_4196_);
    leanh::lean_dec_ref(v___y_4195_);
    leanh::lean_dec(v___y_4194_);
    leanh::lean_dec_ref(v___y_4193_);
    leanh::lean_dec(v___y_4192_);
    leanh::lean_dec_ref(v___y_4191_);
    leanh::lean_dec(v___y_4190_);
    leanh::lean_dec(v___y_4189_);
    leanh::lean_dec_ref(v___y_4188_);
    return v_res_4200_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(
    mut v_f_4201_: *mut leanh::LeanObject,
    mut v_a_u2081_4202_: *mut leanh::LeanObject,
    mut v_a_u2082_4203_: *mut leanh::LeanObject,
    mut v_a_u2083_4204_: *mut leanh::LeanObject,
    mut v___y_4205_: *mut leanh::LeanObject,
    mut v___y_4206_: *mut leanh::LeanObject,
    mut v___y_4207_: *mut leanh::LeanObject,
    mut v___y_4208_: *mut leanh::LeanObject,
    mut v___y_4209_: *mut leanh::LeanObject,
    mut v___y_4210_: *mut leanh::LeanObject,
    mut v___y_4211_: *mut leanh::LeanObject,
    mut v___y_4212_: *mut leanh::LeanObject,
    mut v___y_4213_: *mut leanh::LeanObject,
    mut v___y_4214_: *mut leanh::LeanObject,
    mut v___y_4215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4217_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(v_f_4201_, v_a_u2081_4202_, v_a_u2082_4203_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
    if leanh::lean_obj_tag(v___x_4217_) == 0 {
        let mut v_a_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4218_ = leanh::lean_ctor_get(v___x_4217_, 0);
        leanh::lean_inc(v_a_4218_);
        leanh::lean_dec_ref_known(v___x_4217_, 1);
        v___x_4219_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_4218_, v_a_u2083_4204_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
        return v___x_4219_;
    } else {
        leanh::lean_dec_ref(v_a_u2083_4204_);
        return v___x_4217_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0___boxed(
    mut v_f_4220_: *mut leanh::LeanObject,
    mut v_a_u2081_4221_: *mut leanh::LeanObject,
    mut v_a_u2082_4222_: *mut leanh::LeanObject,
    mut v_a_u2083_4223_: *mut leanh::LeanObject,
    mut v___y_4224_: *mut leanh::LeanObject,
    mut v___y_4225_: *mut leanh::LeanObject,
    mut v___y_4226_: *mut leanh::LeanObject,
    mut v___y_4227_: *mut leanh::LeanObject,
    mut v___y_4228_: *mut leanh::LeanObject,
    mut v___y_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
    mut v___y_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
    mut v___y_4234_: *mut leanh::LeanObject,
    mut v___y_4235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4236_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_f_4220_, v_a_u2081_4221_, v_a_u2082_4222_, v_a_u2083_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
    leanh::lean_dec(v___y_4234_);
    leanh::lean_dec_ref(v___y_4233_);
    leanh::lean_dec(v___y_4232_);
    leanh::lean_dec_ref(v___y_4231_);
    leanh::lean_dec(v___y_4230_);
    leanh::lean_dec_ref(v___y_4229_);
    leanh::lean_dec(v___y_4228_);
    leanh::lean_dec_ref(v___y_4227_);
    leanh::lean_dec(v___y_4226_);
    leanh::lean_dec(v___y_4225_);
    leanh::lean_dec_ref(v___y_4224_);
    return v_res_4236_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(
    mut v_goal_4237_: *mut leanh::LeanObject,
    mut v_ent_4238_: *mut leanh::LeanObject,
    mut v_00_u03c3s_4239_: *mut leanh::LeanObject,
    mut v_H_4240_: *mut leanh::LeanObject,
    mut v_T_4241_: *mut leanh::LeanObject,
    mut v_a_4242_: *mut leanh::LeanObject,
    mut v_a_4243_: *mut leanh::LeanObject,
    mut v_a_4244_: *mut leanh::LeanObject,
    mut v_a_4245_: *mut leanh::LeanObject,
    mut v_a_4246_: *mut leanh::LeanObject,
    mut v_a_4247_: *mut leanh::LeanObject,
    mut v_a_4248_: *mut leanh::LeanObject,
    mut v_a_4249_: *mut leanh::LeanObject,
    mut v_a_4250_: *mut leanh::LeanObject,
    mut v_a_4251_: *mut leanh::LeanObject,
    mut v_a_4252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4260_: u8 = 0;
    let mut v___y_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4270_: u8 = 0;
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4275_: u8 = 0;
    let mut v_a_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4279_: u8 = 0;
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut v_a_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut v___y_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_a_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut v_a_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4313_: u8 = 0;
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_H_4240_);
                v___x_4254_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(
                    v_H_4240_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_,
                );
                if leanh::lean_obj_tag(v___x_4254_) == 0 {
                    v_a_4255_ = leanh::lean_ctor_get(v___x_4254_, 0);
                    leanh::lean_inc(v_a_4255_);
                    leanh::lean_dec_ref_known(v___x_4254_, 1);
                    leanh::lean_inc_ref(v_T_4241_);
                    v___x_4256_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(
                        v_T_4241_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_,
                    );
                    if leanh::lean_obj_tag(v___x_4256_) == 0 {
                        v_a_4257_ = leanh::lean_ctor_get(v___x_4256_, 0);
                        v_isSharedCheck_4301_ =
                            (!leanh::lean_is_exclusive(v___x_4256_)) as u8;
                        if v_isSharedCheck_4301_ == 0 {
                            v___x_4259_ = v___x_4256_;
                            v_isShared_4260_ = v_isSharedCheck_4301_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4257_);
                            leanh::lean_dec(v___x_4256_);
                            v___x_4259_ = leanh::lean_box(0);
                            v_isShared_4260_ = v_isSharedCheck_4301_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4255_);
                        leanh::lean_dec_ref(v_T_4241_);
                        leanh::lean_dec_ref(v_H_4240_);
                        leanh::lean_dec_ref(v_00_u03c3s_4239_);
                        leanh::lean_dec_ref(v_ent_4238_);
                        leanh::lean_dec(v_goal_4237_);
                        v_a_4302_ = leanh::lean_ctor_get(v___x_4256_, 0);
                        v_isSharedCheck_4309_ =
                            (!leanh::lean_is_exclusive(v___x_4256_)) as u8;
                        if v_isSharedCheck_4309_ == 0 {
                            v___x_4304_ = v___x_4256_;
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4302_);
                            leanh::lean_dec(v___x_4256_);
                            v___x_4304_ = leanh::lean_box(0);
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_T_4241_);
                    leanh::lean_dec_ref(v_H_4240_);
                    leanh::lean_dec_ref(v_00_u03c3s_4239_);
                    leanh::lean_dec_ref(v_ent_4238_);
                    leanh::lean_dec(v_goal_4237_);
                    v_a_4310_ = leanh::lean_ctor_get(v___x_4254_, 0);
                    v_isSharedCheck_4317_ = (!leanh::lean_is_exclusive(v___x_4254_)) as u8;
                    if v_isSharedCheck_4317_ == 0 {
                        v___x_4312_ = v___x_4254_;
                        v_isShared_4313_ = v_isSharedCheck_4317_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4310_);
                        leanh::lean_dec(v___x_4254_);
                        v___x_4312_ = leanh::lean_box(0);
                        v_isShared_4313_ = v_isSharedCheck_4317_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4255_) == 0 {
                    if leanh::lean_obj_tag(v_a_4257_) == 0 {
                        leanh::lean_dec_ref(v_T_4241_);
                        leanh::lean_dec_ref(v_H_4240_);
                        leanh::lean_dec_ref(v_00_u03c3s_4239_);
                        leanh::lean_dec_ref(v_ent_4238_);
                        leanh::lean_dec(v_goal_4237_);
                        v___x_4297_ = leanh::lean_box(0);
                        if v_isShared_4260_ == 0 {
                            leanh::lean_ctor_set(v___x_4259_, 0, v___x_4297_);
                            v___x_4299_ = v___x_4259_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_4300_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
                            v___x_4299_ = v_reuseFailAlloc_4300_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4259_);
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4259_);
                    state = 10;
                    continue;
                }
            }
            2 => {
                v___x_4264_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_4238_, v_00_u03c3s_4239_, v___y_4262_, v___y_4263_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
                if leanh::lean_obj_tag(v___x_4264_) == 0 {
                    v_a_4265_ = leanh::lean_ctor_get(v___x_4264_, 0);
                    leanh::lean_inc(v_a_4265_);
                    leanh::lean_dec_ref_known(v___x_4264_, 1);
                    v___x_4266_ = l_Lean_MVarId_replaceTargetDefEq(
                        v_goal_4237_,
                        v_a_4265_,
                        v_a_4249_,
                        v_a_4250_,
                        v_a_4251_,
                        v_a_4252_,
                    );
                    if leanh::lean_obj_tag(v___x_4266_) == 0 {
                        v_a_4267_ = leanh::lean_ctor_get(v___x_4266_, 0);
                        v_isSharedCheck_4275_ =
                            (!leanh::lean_is_exclusive(v___x_4266_)) as u8;
                        if v_isSharedCheck_4275_ == 0 {
                            v___x_4269_ = v___x_4266_;
                            v_isShared_4270_ = v_isSharedCheck_4275_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4267_);
                            leanh::lean_dec(v___x_4266_);
                            v___x_4269_ = leanh::lean_box(0);
                            v_isShared_4270_ = v_isSharedCheck_4275_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4276_ = leanh::lean_ctor_get(v___x_4266_, 0);
                        v_isSharedCheck_4283_ =
                            (!leanh::lean_is_exclusive(v___x_4266_)) as u8;
                        if v_isSharedCheck_4283_ == 0 {
                            v___x_4278_ = v___x_4266_;
                            v_isShared_4279_ = v_isSharedCheck_4283_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4276_);
                            leanh::lean_dec(v___x_4266_);
                            v___x_4278_ = leanh::lean_box(0);
                            v_isShared_4279_ = v_isSharedCheck_4283_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_goal_4237_);
                    v_a_4284_ = leanh::lean_ctor_get(v___x_4264_, 0);
                    v_isSharedCheck_4291_ = (!leanh::lean_is_exclusive(v___x_4264_)) as u8;
                    if v_isSharedCheck_4291_ == 0 {
                        v___x_4286_ = v___x_4264_;
                        v_isShared_4287_ = v_isSharedCheck_4291_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4284_);
                        leanh::lean_dec(v___x_4264_);
                        v___x_4286_ = leanh::lean_box(0);
                        v_isShared_4287_ = v_isSharedCheck_4291_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4271_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4271_, 0, v_a_4267_);
                if v_isShared_4270_ == 0 {
                    leanh::lean_ctor_set(v___x_4269_, 0, v___x_4271_);
                    v___x_4273_ = v___x_4269_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
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
                    v_reuseFailAlloc_4282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
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
                    v_reuseFailAlloc_4290_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4289_;
            }
            9 => {
                if leanh::lean_obj_tag(v_a_4257_) == 0 {
                    v___y_4262_ = v___y_4293_;
                    v___y_4263_ = v_T_4241_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_T_4241_);
                    v_val_4294_ = leanh::lean_ctor_get(v_a_4257_, 0);
                    leanh::lean_inc(v_val_4294_);
                    leanh::lean_dec_ref_known(v_a_4257_, 1);
                    v___y_4262_ = v___y_4293_;
                    v___y_4263_ = v_val_4294_;
                    state = 2;
                    continue;
                }
            }
            10 => {
                if leanh::lean_obj_tag(v_a_4255_) == 0 {
                    v___y_4293_ = v_H_4240_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_H_4240_);
                    v_val_4296_ = leanh::lean_ctor_get(v_a_4255_, 0);
                    leanh::lean_inc(v_val_4296_);
                    leanh::lean_dec_ref_known(v_a_4255_, 1);
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
                    v_reuseFailAlloc_4308_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
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
                    v_reuseFailAlloc_4316_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_goal_4318_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_ent_4319_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3s_4320_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_H_4321_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_T_4322_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_a_4323_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_a_4324_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_a_4325_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_4326_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_4327_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_4328_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_4329_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_4330_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_4331_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_4332_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_4333_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_4334_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4335_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(v_goal_4318_, v_ent_4319_, v_00_u03c3s_4320_, v_H_4321_, v_T_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_);
    leanh::lean_dec(v_a_4333_);
    leanh::lean_dec_ref(v_a_4332_);
    leanh::lean_dec(v_a_4331_);
    leanh::lean_dec_ref(v_a_4330_);
    leanh::lean_dec(v_a_4329_);
    leanh::lean_dec_ref(v_a_4328_);
    leanh::lean_dec(v_a_4327_);
    leanh::lean_dec_ref(v_a_4326_);
    leanh::lean_dec(v_a_4325_);
    leanh::lean_dec(v_a_4324_);
    leanh::lean_dec_ref(v_a_4323_);
    return v_res_4335_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1(
    mut v_f_4336_: *mut leanh::LeanObject,
    mut v_a_4337_: *mut leanh::LeanObject,
    mut v___y_4338_: *mut leanh::LeanObject,
    mut v___y_4339_: *mut leanh::LeanObject,
    mut v___y_4340_: *mut leanh::LeanObject,
    mut v___y_4341_: *mut leanh::LeanObject,
    mut v___y_4342_: *mut leanh::LeanObject,
    mut v___y_4343_: *mut leanh::LeanObject,
    mut v___y_4344_: *mut leanh::LeanObject,
    mut v___y_4345_: *mut leanh::LeanObject,
    mut v___y_4346_: *mut leanh::LeanObject,
    mut v___y_4347_: *mut leanh::LeanObject,
    mut v___y_4348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4350_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_4336_, v_a_4337_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
    return v___x_4350_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___boxed(
    mut v_f_4351_: *mut leanh::LeanObject,
    mut v_a_4352_: *mut leanh::LeanObject,
    mut v___y_4353_: *mut leanh::LeanObject,
    mut v___y_4354_: *mut leanh::LeanObject,
    mut v___y_4355_: *mut leanh::LeanObject,
    mut v___y_4356_: *mut leanh::LeanObject,
    mut v___y_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
    mut v___y_4359_: *mut leanh::LeanObject,
    mut v___y_4360_: *mut leanh::LeanObject,
    mut v___y_4361_: *mut leanh::LeanObject,
    mut v___y_4362_: *mut leanh::LeanObject,
    mut v___y_4363_: *mut leanh::LeanObject,
    mut v___y_4364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4365_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1(v_f_4351_, v_a_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
    leanh::lean_dec(v___y_4363_);
    leanh::lean_dec_ref(v___y_4362_);
    leanh::lean_dec(v___y_4361_);
    leanh::lean_dec_ref(v___y_4360_);
    leanh::lean_dec(v___y_4359_);
    leanh::lean_dec_ref(v___y_4358_);
    leanh::lean_dec(v___y_4357_);
    leanh::lean_dec_ref(v___y_4356_);
    leanh::lean_dec(v___y_4355_);
    leanh::lean_dec(v___y_4354_);
    leanh::lean_dec_ref(v___y_4353_);
    return v_res_4365_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_4366_: *mut leanh::LeanObject,
    mut v_x_4367_: *mut leanh::LeanObject,
    mut v_x_4368_: *mut leanh::LeanObject,
    mut v_x_4369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: u8 = 0;
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: u8 = 0;
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4370_ = leanh::lean_ctor_get(v_x_4366_, 0);
                v_vs_4371_ = leanh::lean_ctor_get(v_x_4366_, 1);
                v_isSharedCheck_4395_ = (!leanh::lean_is_exclusive(v_x_4366_)) as u8;
                if v_isSharedCheck_4395_ == 0 {
                    v___x_4373_ = v_x_4366_;
                    v_isShared_4374_ = v_isSharedCheck_4395_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4371_);
                    leanh::lean_inc(v_ks_4370_);
                    leanh::lean_dec(v_x_4366_);
                    v___x_4373_ = leanh::lean_box(0);
                    v_isShared_4374_ = v_isSharedCheck_4395_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4375_ = lean_array_get_size(v_ks_4370_);
                v___x_4376_ = lean_nat_dec_lt(v_x_4367_, v___x_4375_);
                if v___x_4376_ == 0 {
                    leanh::lean_dec(v_x_4367_);
                    v___x_4377_ = lean_array_push(v_ks_4370_, v_x_4368_);
                    v___x_4378_ = lean_array_push(v_vs_4371_, v_x_4369_);
                    if v_isShared_4374_ == 0 {
                        leanh::lean_ctor_set(v___x_4373_, 1, v___x_4378_);
                        leanh::lean_ctor_set(v___x_4373_, 0, v___x_4377_);
                        v___x_4380_ = v___x_4373_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4381_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4377_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 1, v___x_4378_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_ks_4370_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 1, v_vs_4371_);
                            v___x_4385_ = v_reuseFailAlloc_4389_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4390_ = lean_array_fset(v_ks_4370_, v_x_4367_, v_x_4368_);
                        v___x_4391_ = lean_array_fset(v_vs_4371_, v_x_4367_, v_x_4369_);
                        leanh::lean_dec(v_x_4367_);
                        if v_isShared_4374_ == 0 {
                            leanh::lean_ctor_set(v___x_4373_, 1, v___x_4391_);
                            leanh::lean_ctor_set(v___x_4373_, 0, v___x_4390_);
                            v___x_4393_ = v___x_4373_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4394_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4390_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4394_, 1, v___x_4391_);
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
                v___x_4386_ = leanh::lean_unsigned_to_nat(1);
                v___x_4387_ = lean_nat_add(v_x_4367_, v___x_4386_);
                leanh::lean_dec(v_x_4367_);
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
    mut v_n_4396_: *mut leanh::LeanObject,
    mut v_k_4397_: *mut leanh::LeanObject,
    mut v_v_4398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4399_ = leanh::lean_unsigned_to_nat(0);
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
    v___x_4405_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_4406_ = lean_usize_sub(v___x_4405_, v___x_4404_);
    return v___x_4406_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4407_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4407_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg(
    mut v_x_4408_: *mut leanh::LeanObject,
    mut v_x_4409_: usize,
    mut v_x_4410_: usize,
    mut v_x_4411_: *mut leanh::LeanObject,
    mut v_x_4412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: usize = 0;
    let mut v___x_4415_: usize = 0;
    let mut v___x_4416_: usize = 0;
    let mut v___x_4417_: usize = 0;
    let mut v_j_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: u8 = 0;
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4423_: u8 = 0;
    let mut v_v_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4437_: u8 = 0;
    let mut v___x_4438_: u8 = 0;
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4444_: u8 = 0;
    let mut v_node_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4448_: u8 = 0;
    let mut v___x_4449_: usize = 0;
    let mut v___x_4450_: usize = 0;
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4455_: u8 = 0;
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut v_unused_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4468_: u8 = 0;
    let mut v_ks_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: usize = 0;
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: u8 = 0;
    let mut v_reuseFailAlloc_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4408_) == 0 {
                    v_es_4413_ = leanh::lean_ctor_get(v_x_4408_, 0);
                    v___x_4414_ = 5usize;
                    v___x_4415_ = 1usize;
                    v___x_4416_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4417_ = lean_usize_land(v_x_4409_, v___x_4416_);
                    v_j_4418_ = lean_usize_to_nat(v___x_4417_);
                    v___x_4419_ = lean_array_get_size(v_es_4413_);
                    v___x_4420_ = lean_nat_dec_lt(v_j_4418_, v___x_4419_);
                    if v___x_4420_ == 0 {
                        leanh::lean_dec(v_j_4418_);
                        leanh::lean_dec(v_x_4412_);
                        leanh::lean_dec(v_x_4411_);
                        return v_x_4408_;
                    } else {
                        leanh::lean_inc_ref(v_es_4413_);
                        v_isSharedCheck_4457_ = (!leanh::lean_is_exclusive(v_x_4408_)) as u8;
                        if v_isSharedCheck_4457_ == 0 {
                            v_unused_4458_ = leanh::lean_ctor_get(v_x_4408_, 0);
                            leanh::lean_dec(v_unused_4458_);
                            v___x_4422_ = v_x_4408_;
                            v_isShared_4423_ = v_isSharedCheck_4457_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4408_);
                            v___x_4422_ = leanh::lean_box(0);
                            v_isShared_4423_ = v_isSharedCheck_4457_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4459_ = leanh::lean_ctor_get(v_x_4408_, 0);
                    v_vs_4460_ = leanh::lean_ctor_get(v_x_4408_, 1);
                    v_isSharedCheck_4480_ = (!leanh::lean_is_exclusive(v_x_4408_)) as u8;
                    if v_isSharedCheck_4480_ == 0 {
                        v___x_4462_ = v_x_4408_;
                        v_isShared_4463_ = v_isSharedCheck_4480_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4460_);
                        leanh::lean_inc(v_ks_4459_);
                        leanh::lean_dec(v_x_4408_);
                        v___x_4462_ = leanh::lean_box(0);
                        v_isShared_4463_ = v_isSharedCheck_4480_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4424_ = lean_array_fget(v_es_4413_, v_j_4418_);
                v___x_4425_ = leanh::lean_box(0);
                v_xs_x27_4426_ = lean_array_fset(v_es_4413_, v_j_4418_, v___x_4425_);
                match leanh::lean_obj_tag(v_v_4424_) {
                    0 => {
                        v_key_4433_ = leanh::lean_ctor_get(v_v_4424_, 0);
                        v_val_4434_ = leanh::lean_ctor_get(v_v_4424_, 1);
                        v_isSharedCheck_4444_ = (!leanh::lean_is_exclusive(v_v_4424_)) as u8;
                        if v_isSharedCheck_4444_ == 0 {
                            v___x_4436_ = v_v_4424_;
                            v_isShared_4437_ = v_isSharedCheck_4444_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4434_);
                            leanh::lean_inc(v_key_4433_);
                            leanh::lean_dec(v_v_4424_);
                            v___x_4436_ = leanh::lean_box(0);
                            v_isShared_4437_ = v_isSharedCheck_4444_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4445_ = leanh::lean_ctor_get(v_v_4424_, 0);
                        v_isSharedCheck_4455_ = (!leanh::lean_is_exclusive(v_v_4424_)) as u8;
                        if v_isSharedCheck_4455_ == 0 {
                            v___x_4447_ = v_v_4424_;
                            v_isShared_4448_ = v_isSharedCheck_4455_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4445_);
                            leanh::lean_dec(v_v_4424_);
                            v___x_4447_ = leanh::lean_box(0);
                            v_isShared_4448_ = v_isSharedCheck_4455_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4456_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4456_, 0, v_x_4411_);
                        leanh::lean_ctor_set(v___x_4456_, 1, v_x_4412_);
                        v___y_4428_ = v___x_4456_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4429_ = lean_array_fset(v_xs_x27_4426_, v_j_4418_, v___y_4428_);
                leanh::lean_dec(v_j_4418_);
                if v_isShared_4423_ == 0 {
                    leanh::lean_ctor_set(v___x_4422_, 0, v___x_4429_);
                    v___x_4431_ = v___x_4422_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4432_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4429_);
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
                    leanh::lean_del_object(v___x_4436_);
                    v___x_4439_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4433_,
                        v_val_4434_,
                        v_x_4411_,
                        v_x_4412_,
                    );
                    v___x_4440_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4440_, 0, v___x_4439_);
                    v___y_4428_ = v___x_4440_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4434_);
                    leanh::lean_dec(v_key_4433_);
                    if v_isShared_4437_ == 0 {
                        leanh::lean_ctor_set(v___x_4436_, 1, v_x_4412_);
                        leanh::lean_ctor_set(v___x_4436_, 0, v_x_4411_);
                        v___x_4442_ = v___x_4436_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4443_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_x_4411_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4443_, 1, v_x_4412_);
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
                    leanh::lean_ctor_set(v___x_4447_, 0, v___x_4451_);
                    v___x_4453_ = v___x_4447_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4454_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4451_);
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
                    v_reuseFailAlloc_4479_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_ks_4459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_vs_4460_);
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
                    v___x_4477_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4478_ = lean_nat_dec_lt(v___x_4476_, v___x_4477_);
                    leanh::lean_dec(v___x_4476_);
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
                    v_ks_4469_ = leanh::lean_ctor_get(v_newNode_4466_, 0);
                    leanh::lean_inc_ref(v_ks_4469_);
                    v_vs_4470_ = leanh::lean_ctor_get(v_newNode_4466_, 1);
                    leanh::lean_inc_ref(v_vs_4470_);
                    leanh::lean_dec_ref(v_newNode_4466_);
                    v___x_4471_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4472_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_4473_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4410_, v_ks_4469_, v_vs_4470_, v___x_4471_, v___x_4472_);
                    leanh::lean_dec_ref(v_vs_4470_);
                    leanh::lean_dec_ref(v_ks_4469_);
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
    mut v_keys_4482_: *mut leanh::LeanObject,
    mut v_vals_4483_: *mut leanh::LeanObject,
    mut v_i_4484_: *mut leanh::LeanObject,
    mut v_entries_4485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: u8 = 0;
    let mut v_k_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: u64 = 0;
    let mut v_h_4491_: usize = 0;
    let mut v___x_4492_: usize = 0;
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: usize = 0;
    let mut v___x_4495_: usize = 0;
    let mut v___x_4496_: usize = 0;
    let mut v_h_4497_: usize = 0;
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4486_ = lean_array_get_size(v_keys_4482_);
                v___x_4487_ = lean_nat_dec_lt(v_i_4484_, v___x_4486_);
                if v___x_4487_ == 0 {
                    leanh::lean_dec(v_i_4484_);
                    return v_entries_4485_;
                } else {
                    v_k_4488_ = lean_array_fget_borrowed(v_keys_4482_, v_i_4484_);
                    v_v_4489_ = lean_array_fget_borrowed(v_vals_4483_, v_i_4484_);
                    v___x_4490_ = l_Lean_instHashableMVarId_hash(v_k_4488_);
                    v_h_4491_ = lean_uint64_to_usize(v___x_4490_);
                    v___x_4492_ = 5usize;
                    v___x_4493_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4494_ = 1usize;
                    v___x_4495_ = lean_usize_sub(v_depth_4481_, v___x_4494_);
                    v___x_4496_ = lean_usize_mul(v___x_4492_, v___x_4495_);
                    v_h_4497_ = lean_usize_shift_right(v_h_4491_, v___x_4496_);
                    v___x_4498_ = lean_nat_add(v_i_4484_, v___x_4493_);
                    leanh::lean_dec(v_i_4484_);
                    leanh::lean_inc(v_v_4489_);
                    leanh::lean_inc(v_k_4488_);
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
    mut v_depth_4501_: *mut leanh::LeanObject,
    mut v_keys_4502_: *mut leanh::LeanObject,
    mut v_vals_4503_: *mut leanh::LeanObject,
    mut v_i_4504_: *mut leanh::LeanObject,
    mut v_entries_4505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4506_: usize = 0;
    let mut v_res_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4506_ = leanh::lean_unbox_usize(v_depth_4501_);
    leanh::lean_dec(v_depth_4501_);
    v_res_4507_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_4506_, v_keys_4502_, v_vals_4503_, v_i_4504_, v_entries_4505_);
    leanh::lean_dec_ref(v_vals_4503_);
    leanh::lean_dec_ref(v_keys_4502_);
    return v_res_4507_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4508_: *mut leanh::LeanObject,
    mut v_x_4509_: *mut leanh::LeanObject,
    mut v_x_4510_: *mut leanh::LeanObject,
    mut v_x_4511_: *mut leanh::LeanObject,
    mut v_x_4512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_28835__boxed_4513_: usize = 0;
    let mut v_x_28836__boxed_4514_: usize = 0;
    let mut v_res_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_28835__boxed_4513_ = leanh::lean_unbox_usize(v_x_4509_);
    leanh::lean_dec(v_x_4509_);
    v_x_28836__boxed_4514_ = leanh::lean_unbox_usize(v_x_4510_);
    leanh::lean_dec(v_x_4510_);
    v_res_4515_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg(v_x_4508_, v_x_28835__boxed_4513_, v_x_28836__boxed_4514_, v_x_4511_, v_x_4512_);
    return v_res_4515_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0___redArg(
    mut v_x_4516_: *mut leanh::LeanObject,
    mut v_x_4517_: *mut leanh::LeanObject,
    mut v_x_4518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4519_: u64 = 0;
    let mut v___x_4520_: usize = 0;
    let mut v___x_4521_: usize = 0;
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4519_ = l_Lean_instHashableMVarId_hash(v_x_4517_);
    v___x_4520_ = lean_uint64_to_usize(v___x_4519_);
    v___x_4521_ = 1usize;
    v___x_4522_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg(v_x_4516_, v___x_4520_, v___x_4521_, v_x_4517_, v_x_4518_);
    return v___x_4522_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___redArg(
    mut v_mvarId_4523_: *mut leanh::LeanObject,
    mut v_val_4524_: *mut leanh::LeanObject,
    mut v___y_4525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4535_: u8 = 0;
    let mut v_depth_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4548_: u8 = 0;
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut v_isSharedCheck_4560_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4527_ = lean_st_ref_take(v___y_4525_);
                v_mctx_4528_ = leanh::lean_ctor_get(v___x_4527_, 0);
                v_cache_4529_ = leanh::lean_ctor_get(v___x_4527_, 1);
                v_zetaDeltaFVarIds_4530_ = leanh::lean_ctor_get(v___x_4527_, 2);
                v_postponed_4531_ = leanh::lean_ctor_get(v___x_4527_, 3);
                v_diag_4532_ = leanh::lean_ctor_get(v___x_4527_, 4);
                v_isSharedCheck_4560_ = (!leanh::lean_is_exclusive(v___x_4527_)) as u8;
                if v_isSharedCheck_4560_ == 0 {
                    v___x_4534_ = v___x_4527_;
                    v_isShared_4535_ = v_isSharedCheck_4560_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4532_);
                    leanh::lean_inc(v_postponed_4531_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4530_);
                    leanh::lean_inc(v_cache_4529_);
                    leanh::lean_inc(v_mctx_4528_);
                    leanh::lean_dec(v___x_4527_);
                    v___x_4534_ = leanh::lean_box(0);
                    v_isShared_4535_ = v_isSharedCheck_4560_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4536_ = leanh::lean_ctor_get(v_mctx_4528_, 0);
                v_levelAssignDepth_4537_ = leanh::lean_ctor_get(v_mctx_4528_, 1);
                v_lmvarCounter_4538_ = leanh::lean_ctor_get(v_mctx_4528_, 2);
                v_mvarCounter_4539_ = leanh::lean_ctor_get(v_mctx_4528_, 3);
                v_lDecls_4540_ = leanh::lean_ctor_get(v_mctx_4528_, 4);
                v_decls_4541_ = leanh::lean_ctor_get(v_mctx_4528_, 5);
                v_userNames_4542_ = leanh::lean_ctor_get(v_mctx_4528_, 6);
                v_lAssignment_4543_ = leanh::lean_ctor_get(v_mctx_4528_, 7);
                v_eAssignment_4544_ = leanh::lean_ctor_get(v_mctx_4528_, 8);
                v_dAssignment_4545_ = leanh::lean_ctor_get(v_mctx_4528_, 9);
                v_isSharedCheck_4559_ = (!leanh::lean_is_exclusive(v_mctx_4528_)) as u8;
                if v_isSharedCheck_4559_ == 0 {
                    v___x_4547_ = v_mctx_4528_;
                    v_isShared_4548_ = v_isSharedCheck_4559_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_4545_);
                    leanh::lean_inc(v_eAssignment_4544_);
                    leanh::lean_inc(v_lAssignment_4543_);
                    leanh::lean_inc(v_userNames_4542_);
                    leanh::lean_inc(v_decls_4541_);
                    leanh::lean_inc(v_lDecls_4540_);
                    leanh::lean_inc(v_mvarCounter_4539_);
                    leanh::lean_inc(v_lmvarCounter_4538_);
                    leanh::lean_inc(v_levelAssignDepth_4537_);
                    leanh::lean_inc(v_depth_4536_);
                    leanh::lean_dec(v_mctx_4528_);
                    v___x_4547_ = leanh::lean_box(0);
                    v_isShared_4548_ = v_isSharedCheck_4559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4549_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0___redArg(v_eAssignment_4544_, v_mvarId_4523_, v_val_4524_);
                if v_isShared_4548_ == 0 {
                    leanh::lean_ctor_set(v___x_4547_, 8, v___x_4549_);
                    v___x_4551_ = v___x_4547_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_depth_4536_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4558_,
                        1,
                        v_levelAssignDepth_4537_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 2, v_lmvarCounter_4538_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 3, v_mvarCounter_4539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 4, v_lDecls_4540_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 5, v_decls_4541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 6, v_userNames_4542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 7, v_lAssignment_4543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 8, v___x_4549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 9, v_dAssignment_4545_);
                    v___x_4551_ = v_reuseFailAlloc_4558_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4535_ == 0 {
                    leanh::lean_ctor_set(v___x_4534_, 0, v___x_4551_);
                    v___x_4553_ = v___x_4534_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4557_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_cache_4529_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4557_,
                        2,
                        v_zetaDeltaFVarIds_4530_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 3, v_postponed_4531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 4, v_diag_4532_);
                    v___x_4553_ = v_reuseFailAlloc_4557_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4554_ = lean_st_ref_set(v___y_4525_, v___x_4553_);
                v___x_4555_ = leanh::lean_box(0);
                v___x_4556_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4556_, 0, v___x_4555_);
                return v___x_4556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___redArg___boxed(
    mut v_mvarId_4561_: *mut leanh::LeanObject,
    mut v_val_4562_: *mut leanh::LeanObject,
    mut v___y_4563_: *mut leanh::LeanObject,
    mut v___y_4564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4565_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___redArg(v_mvarId_4561_, v_val_4562_, v___y_4563_);
    leanh::lean_dec(v___y_4563_);
    return v_res_4565_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4575_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__3;
    v___x_4576_ = l_Lean_stringToMessageData(v___x_4575_);
    return v___x_4576_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4580_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__6;
    v___x_4581_ = l_Lean_stringToMessageData(v___x_4580_);
    return v___x_4581_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails(
    mut v_goal_4582_: *mut leanh::LeanObject,
    mut v_ent_4583_: *mut leanh::LeanObject,
    mut v_00_u03c3s_4584_: *mut leanh::LeanObject,
    mut v_H_4585_: *mut leanh::LeanObject,
    mut v_T_4586_: *mut leanh::LeanObject,
    mut v_a_4587_: *mut leanh::LeanObject,
    mut v_a_4588_: *mut leanh::LeanObject,
    mut v_a_4589_: *mut leanh::LeanObject,
    mut v_a_4590_: *mut leanh::LeanObject,
    mut v_a_4591_: *mut leanh::LeanObject,
    mut v_a_4592_: *mut leanh::LeanObject,
    mut v_a_4593_: *mut leanh::LeanObject,
    mut v_a_4594_: *mut leanh::LeanObject,
    mut v_a_4595_: *mut leanh::LeanObject,
    mut v_a_4596_: *mut leanh::LeanObject,
    mut v_a_4597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4601_: u8 = 0;
    let mut v___y_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4627_: u8 = 0;
    let mut v_unused_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4643_: u8 = 0;
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4648_: u8 = 0;
    let mut v_val_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4652_: u8 = 0;
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4660_: u8 = 0;
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4665_: u8 = 0;
    let mut v_a_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4669_: u8 = 0;
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4673_: u8 = 0;
    let mut v_options_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4675_: u8 = 0;
    let mut v_inheritedTraceOptions_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: u8 = 0;
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4686_: u8 = 0;
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4690_: u8 = 0;
    let mut v___y_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4724_: u8 = 0;
    let mut v_trackZetaDelta_4725_: u8 = 0;
    let mut v_zetaDeltaSet_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4732_: u8 = 0;
    let mut v_inTypeClassResolution_4733_: u8 = 0;
    let mut v_cacheInferType_4734_: u8 = 0;
    let mut v___x_4735_: u8 = 0;
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: u64 = 0;
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: u8 = 0;
    let mut v_a_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: u8 = 0;
    let mut v_a_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4751_: u8 = 0;
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4755_: u8 = 0;
    let mut v_reuseFailAlloc_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4757_: u8 = 0;
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: u8 = 0;
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4767_: u8 = 0;
    let mut v___x_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4599_ = leanh::lean_ctor_get(v_a_4596_, 2);
                v_inheritedTraceOptions_4600_ = leanh::lean_ctor_get(v_a_4596_, 13);
                v_hasTrace_4601_ = leanh::lean_ctor_get_uint8(
                    v_options_4599_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                    v___x_4758_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
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
                        v___x_4760_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__7);
                        leanh::lean_inc(v_goal_4582_);
                        v___x_4761_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4761_, 0, v_goal_4582_);
                        v___x_4762_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4762_, 0, v___x_4760_);
                        leanh::lean_ctor_set(v___x_4762_, 1, v___x_4761_);
                        v___x_4763_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_4629_, v___x_4762_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
                        if leanh::lean_obj_tag(v___x_4763_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4763_, 1);
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
                            leanh::lean_dec_ref(v_T_4586_);
                            leanh::lean_dec_ref(v_H_4585_);
                            leanh::lean_dec_ref(v_00_u03c3s_4584_);
                            leanh::lean_dec(v_goal_4582_);
                            v_a_4764_ = leanh::lean_ctor_get(v___x_4763_, 0);
                            v_isSharedCheck_4771_ =
                                (!leanh::lean_is_exclusive(v___x_4763_)) as u8;
                            if v_isSharedCheck_4771_ == 0 {
                                v___x_4766_ = v___x_4763_;
                                v_isShared_4767_ = v_isSharedCheck_4771_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4764_);
                                leanh::lean_dec(v___x_4763_);
                                v___x_4766_ = leanh::lean_box(0);
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
                v_isSharedCheck_4627_ = (!leanh::lean_is_exclusive(v___x_4619_)) as u8;
                if v_isSharedCheck_4627_ == 0 {
                    v_unused_4628_ = leanh::lean_ctor_get(v___x_4619_, 0);
                    leanh::lean_dec(v_unused_4628_);
                    v___x_4621_ = v___x_4619_;
                    v_isShared_4622_ = v_isSharedCheck_4627_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4619_);
                    v___x_4621_ = leanh::lean_box(0);
                    v_isShared_4622_ = v_isSharedCheck_4627_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_4603_);
                v___x_4623_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4623_, 0, v___y_4603_);
                if v_isShared_4622_ == 0 {
                    leanh::lean_ctor_set(v___x_4621_, 0, v___x_4623_);
                    v___x_4625_ = v___x_4621_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4626_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
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
                    leanh::lean_dec_ref(v_H_4585_);
                    leanh::lean_dec_ref(v_00_u03c3s_4584_);
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
                    if leanh::lean_obj_tag(v___x_4644_) == 0 {
                        v_a_4645_ = leanh::lean_ctor_get(v___x_4644_, 0);
                        v_isSharedCheck_4665_ =
                            (!leanh::lean_is_exclusive(v___x_4644_)) as u8;
                        if v_isSharedCheck_4665_ == 0 {
                            v___x_4647_ = v___x_4644_;
                            v_isShared_4648_ = v_isSharedCheck_4665_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4645_);
                            leanh::lean_dec(v___x_4644_);
                            v___x_4647_ = leanh::lean_box(0);
                            v_isShared_4648_ = v_isSharedCheck_4665_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_4666_ = leanh::lean_ctor_get(v___x_4644_, 0);
                        v_isSharedCheck_4673_ =
                            (!leanh::lean_is_exclusive(v___x_4644_)) as u8;
                        if v_isSharedCheck_4673_ == 0 {
                            v___x_4668_ = v___x_4644_;
                            v_isShared_4669_ = v_isSharedCheck_4673_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4666_);
                            leanh::lean_dec(v___x_4644_);
                            v___x_4668_ = leanh::lean_box(0);
                            v_isShared_4669_ = v_isSharedCheck_4673_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v_options_4674_ = leanh::lean_ctor_get(v___y_4631_, 2);
                    v_hasTrace_4675_ = leanh::lean_ctor_get_uint8(
                        v_options_4674_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                            leanh::lean_ctor_get(v___y_4631_, 13);
                        v___x_4677_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
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
                            v___x_4679_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__4);
                            leanh::lean_inc(v_goal_4582_);
                            v___x_4680_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4680_, 0, v_goal_4582_);
                            v___x_4681_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4681_, 0, v___x_4679_);
                            leanh::lean_ctor_set(v___x_4681_, 1, v___x_4680_);
                            v___x_4682_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_4629_, v___x_4681_, v___y_4636_, v___y_4633_, v___y_4631_, v___y_4634_);
                            if leanh::lean_obj_tag(v___x_4682_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4682_, 1);
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
                                leanh::lean_dec_ref(v_H_4585_);
                                leanh::lean_dec_ref(v_00_u03c3s_4584_);
                                leanh::lean_dec(v_goal_4582_);
                                v_a_4683_ = leanh::lean_ctor_get(v___x_4682_, 0);
                                v_isSharedCheck_4690_ =
                                    (!leanh::lean_is_exclusive(v___x_4682_)) as u8;
                                if v_isSharedCheck_4690_ == 0 {
                                    v___x_4685_ = v___x_4682_;
                                    v_isShared_4686_ = v_isSharedCheck_4690_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4683_);
                                    leanh::lean_dec(v___x_4682_);
                                    v___x_4685_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v_a_4645_) == 1 {
                    v_val_4649_ = leanh::lean_ctor_get(v_a_4645_, 0);
                    v_isSharedCheck_4660_ = (!leanh::lean_is_exclusive(v_a_4645_)) as u8;
                    if v_isSharedCheck_4660_ == 0 {
                        v___x_4651_ = v_a_4645_;
                        v_isShared_4652_ = v_isSharedCheck_4660_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4649_);
                        leanh::lean_dec(v_a_4645_);
                        v___x_4651_ = leanh::lean_box(0);
                        v_isShared_4652_ = v_isSharedCheck_4660_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4645_);
                    v___x_4661_ = leanh::lean_box(0);
                    if v_isShared_4648_ == 0 {
                        leanh::lean_ctor_set(v___x_4647_, 0, v___x_4661_);
                        v___x_4663_ = v___x_4647_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4664_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4661_);
                        v___x_4663_ = v_reuseFailAlloc_4664_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                leanh::lean_inc(v___y_4639_);
                v___x_4653_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4653_, 0, v_val_4649_);
                leanh::lean_ctor_set(v___x_4653_, 1, v___y_4639_);
                if v_isShared_4652_ == 0 {
                    leanh::lean_ctor_set(v___x_4651_, 0, v___x_4653_);
                    v___x_4655_ = v___x_4651_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4659_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4653_);
                    v___x_4655_ = v_reuseFailAlloc_4659_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4648_ == 0 {
                    leanh::lean_ctor_set(v___x_4647_, 0, v___x_4655_);
                    v___x_4657_ = v___x_4647_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4658_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4655_);
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
                    v_reuseFailAlloc_4672_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
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
                    v_reuseFailAlloc_4689_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
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
                v_foApprox_4704_ = leanh::lean_ctor_get_uint8(v___x_4703_, 0 as u32);
                v_ctxApprox_4705_ = leanh::lean_ctor_get_uint8(v___x_4703_, 1 as u32);
                v_quasiPatternApprox_4706_ =
                    leanh::lean_ctor_get_uint8(v___x_4703_, 2 as u32);
                v_constApprox_4707_ = leanh::lean_ctor_get_uint8(v___x_4703_, 3 as u32);
                v_isDefEqStuckEx_4708_ = leanh::lean_ctor_get_uint8(v___x_4703_, 4 as u32);
                v_unificationHints_4709_ = leanh::lean_ctor_get_uint8(v___x_4703_, 5 as u32);
                v_proofIrrelevance_4710_ = leanh::lean_ctor_get_uint8(v___x_4703_, 6 as u32);
                v_offsetCnstrs_4711_ = leanh::lean_ctor_get_uint8(v___x_4703_, 8 as u32);
                v_transparency_4712_ = leanh::lean_ctor_get_uint8(v___x_4703_, 9 as u32);
                v_etaStruct_4713_ = leanh::lean_ctor_get_uint8(v___x_4703_, 10 as u32);
                v_univApprox_4714_ = leanh::lean_ctor_get_uint8(v___x_4703_, 11 as u32);
                v_iota_4715_ = leanh::lean_ctor_get_uint8(v___x_4703_, 12 as u32);
                v_beta_4716_ = leanh::lean_ctor_get_uint8(v___x_4703_, 13 as u32);
                v_proj_4717_ = leanh::lean_ctor_get_uint8(v___x_4703_, 14 as u32);
                v_zeta_4718_ = leanh::lean_ctor_get_uint8(v___x_4703_, 15 as u32);
                v_zetaDelta_4719_ = leanh::lean_ctor_get_uint8(v___x_4703_, 16 as u32);
                v_zetaUnused_4720_ = leanh::lean_ctor_get_uint8(v___x_4703_, 17 as u32);
                v_zetaHave_4721_ = leanh::lean_ctor_get_uint8(v___x_4703_, 18 as u32);
                v_isSharedCheck_4757_ = (!leanh::lean_is_exclusive(v___x_4703_)) as u8;
                if v_isSharedCheck_4757_ == 0 {
                    v___x_4723_ = v___x_4703_;
                    v_isShared_4724_ = v_isSharedCheck_4757_;
                    state = 15;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4703_);
                    v___x_4723_ = leanh::lean_box(0);
                    v_isShared_4724_ = v_isSharedCheck_4757_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_trackZetaDelta_4725_ = leanh::lean_ctor_get_uint8(
                    v___y_4699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4726_ = leanh::lean_ctor_get(v___y_4699_, 1);
                v_lctx_4727_ = leanh::lean_ctor_get(v___y_4699_, 2);
                v_localInstances_4728_ = leanh::lean_ctor_get(v___y_4699_, 3);
                v_defEqCtx_x3f_4729_ = leanh::lean_ctor_get(v___y_4699_, 4);
                v_synthPendingDepth_4730_ = leanh::lean_ctor_get(v___y_4699_, 5);
                v_canUnfold_x3f_4731_ = leanh::lean_ctor_get(v___y_4699_, 6);
                v_univApprox_4732_ = leanh::lean_ctor_get_uint8(
                    v___y_4699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4733_ = leanh::lean_ctor_get_uint8(
                    v___y_4699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4734_ = leanh::lean_ctor_get_uint8(
                    v___y_4699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_4735_ = 1;
                if v_isShared_4724_ == 0 {
                    v___x_4737_ = v___x_4723_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4756_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        0 as u32,
                        v_foApprox_4704_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        1 as u32,
                        v_ctxApprox_4705_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        2 as u32,
                        v_quasiPatternApprox_4706_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        3 as u32,
                        v_constApprox_4707_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        4 as u32,
                        v_isDefEqStuckEx_4708_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        5 as u32,
                        v_unificationHints_4709_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        6 as u32,
                        v_proofIrrelevance_4710_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        8 as u32,
                        v_offsetCnstrs_4711_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        9 as u32,
                        v_transparency_4712_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        10 as u32,
                        v_etaStruct_4713_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        11 as u32,
                        v_univApprox_4714_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        12 as u32,
                        v_iota_4715_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        13 as u32,
                        v_beta_4716_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        14 as u32,
                        v_proj_4717_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        15 as u32,
                        v_zeta_4718_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        16 as u32,
                        v_zetaDelta_4719_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4756_,
                        17 as u32,
                        v_zetaUnused_4720_,
                    );
                    leanh::lean_ctor_set_uint8(
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
                leanh::lean_ctor_set_uint8(v___x_4737_, 7 as u32, v___x_4735_);
                v___x_4738_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4737_);
                v___x_4739_ = leanh::lean_box(0);
                v___x_4740_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails___closed__5;
                v___x_4741_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_4741_, 0, v___x_4737_);
                leanh::lean_ctor_set_uint64(
                    v___x_4741_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4738_,
                );
                leanh::lean_inc(v_canUnfold_x3f_4731_);
                leanh::lean_inc(v_synthPendingDepth_4730_);
                leanh::lean_inc(v_defEqCtx_x3f_4729_);
                leanh::lean_inc_ref(v_localInstances_4728_);
                leanh::lean_inc_ref(v_lctx_4727_);
                leanh::lean_inc(v_zetaDeltaSet_4726_);
                v___x_4742_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_4742_, 0, v___x_4741_);
                leanh::lean_ctor_set(v___x_4742_, 1, v_zetaDeltaSet_4726_);
                leanh::lean_ctor_set(v___x_4742_, 2, v_lctx_4727_);
                leanh::lean_ctor_set(v___x_4742_, 3, v_localInstances_4728_);
                leanh::lean_ctor_set(v___x_4742_, 4, v_defEqCtx_x3f_4729_);
                leanh::lean_ctor_set(v___x_4742_, 5, v_synthPendingDepth_4730_);
                leanh::lean_ctor_set(v___x_4742_, 6, v_canUnfold_x3f_4731_);
                leanh::lean_ctor_set_uint8(
                    v___x_4742_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4725_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4742_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4732_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4742_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4733_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4742_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4734_,
                );
                leanh::lean_inc_ref(v_H_4585_);
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
                leanh::lean_dec_ref_known(v___x_4742_, 7);
                if leanh::lean_obj_tag(v___x_4743_) == 0 {
                    v_a_4744_ = leanh::lean_ctor_get(v___x_4743_, 0);
                    leanh::lean_inc(v_a_4744_);
                    leanh::lean_dec_ref_known(v___x_4743_, 1);
                    v___x_4745_ = (leanh::lean_unbox(v_a_4744_) as u8);
                    leanh::lean_dec(v_a_4744_);
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
                    if leanh::lean_obj_tag(v___x_4743_) == 0 {
                        v_a_4746_ = leanh::lean_ctor_get(v___x_4743_, 0);
                        leanh::lean_inc(v_a_4746_);
                        leanh::lean_dec_ref_known(v___x_4743_, 1);
                        v___x_4747_ = (leanh::lean_unbox(v_a_4746_) as u8);
                        leanh::lean_dec(v_a_4746_);
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
                        leanh::lean_dec_ref(v_H_4585_);
                        leanh::lean_dec_ref(v_00_u03c3s_4584_);
                        leanh::lean_dec(v_goal_4582_);
                        v_a_4748_ = leanh::lean_ctor_get(v___x_4743_, 0);
                        v_isSharedCheck_4755_ =
                            (!leanh::lean_is_exclusive(v___x_4743_)) as u8;
                        if v_isSharedCheck_4755_ == 0 {
                            v___x_4750_ = v___x_4743_;
                            v_isShared_4751_ = v_isSharedCheck_4755_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4748_);
                            leanh::lean_dec(v___x_4743_);
                            v___x_4750_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4754_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
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
                    v_reuseFailAlloc_4770_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_goal_4772_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_ent_4773_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3s_4774_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_H_4775_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_T_4776_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_a_4777_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_a_4778_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_a_4779_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_4780_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_4781_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_4782_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_4783_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_4784_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_4785_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_4786_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_4787_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_4788_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4789_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails(v_goal_4772_, v_ent_4773_, v_00_u03c3s_4774_, v_H_4775_, v_T_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_);
    leanh::lean_dec(v_a_4787_);
    leanh::lean_dec_ref(v_a_4786_);
    leanh::lean_dec(v_a_4785_);
    leanh::lean_dec_ref(v_a_4784_);
    leanh::lean_dec(v_a_4783_);
    leanh::lean_dec_ref(v_a_4782_);
    leanh::lean_dec(v_a_4781_);
    leanh::lean_dec_ref(v_a_4780_);
    leanh::lean_dec(v_a_4779_);
    leanh::lean_dec(v_a_4778_);
    leanh::lean_dec_ref(v_a_4777_);
    leanh::lean_dec_ref(v_ent_4773_);
    return v_res_4789_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0(
    mut v_mvarId_4790_: *mut leanh::LeanObject,
    mut v_val_4791_: *mut leanh::LeanObject,
    mut v___y_4792_: *mut leanh::LeanObject,
    mut v___y_4793_: *mut leanh::LeanObject,
    mut v___y_4794_: *mut leanh::LeanObject,
    mut v___y_4795_: *mut leanh::LeanObject,
    mut v___y_4796_: *mut leanh::LeanObject,
    mut v___y_4797_: *mut leanh::LeanObject,
    mut v___y_4798_: *mut leanh::LeanObject,
    mut v___y_4799_: *mut leanh::LeanObject,
    mut v___y_4800_: *mut leanh::LeanObject,
    mut v___y_4801_: *mut leanh::LeanObject,
    mut v___y_4802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4804_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___redArg(v_mvarId_4790_, v_val_4791_, v___y_4800_);
    return v___x_4804_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0___boxed(
    mut v_mvarId_4805_: *mut leanh::LeanObject,
    mut v_val_4806_: *mut leanh::LeanObject,
    mut v___y_4807_: *mut leanh::LeanObject,
    mut v___y_4808_: *mut leanh::LeanObject,
    mut v___y_4809_: *mut leanh::LeanObject,
    mut v___y_4810_: *mut leanh::LeanObject,
    mut v___y_4811_: *mut leanh::LeanObject,
    mut v___y_4812_: *mut leanh::LeanObject,
    mut v___y_4813_: *mut leanh::LeanObject,
    mut v___y_4814_: *mut leanh::LeanObject,
    mut v___y_4815_: *mut leanh::LeanObject,
    mut v___y_4816_: *mut leanh::LeanObject,
    mut v___y_4817_: *mut leanh::LeanObject,
    mut v___y_4818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4819_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0(v_mvarId_4805_, v_val_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_);
    leanh::lean_dec(v___y_4817_);
    leanh::lean_dec_ref(v___y_4816_);
    leanh::lean_dec(v___y_4815_);
    leanh::lean_dec_ref(v___y_4814_);
    leanh::lean_dec(v___y_4813_);
    leanh::lean_dec_ref(v___y_4812_);
    leanh::lean_dec(v___y_4811_);
    leanh::lean_dec_ref(v___y_4810_);
    leanh::lean_dec(v___y_4809_);
    leanh::lean_dec(v___y_4808_);
    leanh::lean_dec_ref(v___y_4807_);
    return v_res_4819_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0(
    mut v_00_u03b2_4820_: *mut leanh::LeanObject,
    mut v_x_4821_: *mut leanh::LeanObject,
    mut v_x_4822_: *mut leanh::LeanObject,
    mut v_x_4823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4824_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0___redArg(v_x_4821_, v_x_4822_, v_x_4823_);
    return v___x_4824_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4825_: *mut leanh::LeanObject,
    mut v_x_4826_: *mut leanh::LeanObject,
    mut v_x_4827_: usize,
    mut v_x_4828_: usize,
    mut v_x_4829_: *mut leanh::LeanObject,
    mut v_x_4830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___redArg(v_x_4826_, v_x_4827_, v_x_4828_, v_x_4829_, v_x_4830_);
    return v___x_4831_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4832_: *mut leanh::LeanObject,
    mut v_x_4833_: *mut leanh::LeanObject,
    mut v_x_4834_: *mut leanh::LeanObject,
    mut v_x_4835_: *mut leanh::LeanObject,
    mut v_x_4836_: *mut leanh::LeanObject,
    mut v_x_4837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_29457__boxed_4838_: usize = 0;
    let mut v_x_29458__boxed_4839_: usize = 0;
    let mut v_res_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_29457__boxed_4838_ = leanh::lean_unbox_usize(v_x_4834_);
    leanh::lean_dec(v_x_4834_);
    v_x_29458__boxed_4839_ = leanh::lean_unbox_usize(v_x_4835_);
    leanh::lean_dec(v_x_4835_);
    v_res_4840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1(v_00_u03b2_4832_, v_x_4833_, v_x_29457__boxed_4838_, v_x_29458__boxed_4839_, v_x_4836_, v_x_4837_);
    return v_res_4840_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4841_: *mut leanh::LeanObject,
    mut v_n_4842_: *mut leanh::LeanObject,
    mut v_k_4843_: *mut leanh::LeanObject,
    mut v_v_4844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4845_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2___redArg(v_n_4842_, v_k_4843_, v_v_4844_);
    return v___x_4845_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4846_: *mut leanh::LeanObject,
    mut v_depth_4847_: usize,
    mut v_keys_4848_: *mut leanh::LeanObject,
    mut v_vals_4849_: *mut leanh::LeanObject,
    mut v_heq_4850_: *mut leanh::LeanObject,
    mut v_i_4851_: *mut leanh::LeanObject,
    mut v_entries_4852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4853_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_4847_, v_keys_4848_, v_vals_4849_, v_i_4851_, v_entries_4852_);
    return v___x_4853_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4854_: *mut leanh::LeanObject,
    mut v_depth_4855_: *mut leanh::LeanObject,
    mut v_keys_4856_: *mut leanh::LeanObject,
    mut v_vals_4857_: *mut leanh::LeanObject,
    mut v_heq_4858_: *mut leanh::LeanObject,
    mut v_i_4859_: *mut leanh::LeanObject,
    mut v_entries_4860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4861_: usize = 0;
    let mut v_res_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4861_ = leanh::lean_unbox_usize(v_depth_4855_);
    leanh::lean_dec(v_depth_4855_);
    v_res_4862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4854_, v_depth_boxed_4861_, v_keys_4856_, v_vals_4857_, v_heq_4858_, v_i_4859_, v_entries_4860_);
    leanh::lean_dec_ref(v_vals_4857_);
    leanh::lean_dec_ref(v_keys_4856_);
    return v_res_4862_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_4863_: *mut leanh::LeanObject,
    mut v_x_4864_: *mut leanh::LeanObject,
    mut v_x_4865_: *mut leanh::LeanObject,
    mut v_x_4866_: *mut leanh::LeanObject,
    mut v_x_4867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4868_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4864_, v_x_4865_, v_x_4866_, v_x_4867_);
    return v___x_4868_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(
    mut v_args_4869_: *mut leanh::LeanObject,
    mut v_endIdx_4870_: *mut leanh::LeanObject,
    mut v_b_4871_: *mut leanh::LeanObject,
    mut v_i_4872_: *mut leanh::LeanObject,
    mut v___y_4873_: *mut leanh::LeanObject,
    mut v___y_4874_: *mut leanh::LeanObject,
    mut v___y_4875_: *mut leanh::LeanObject,
    mut v___y_4876_: *mut leanh::LeanObject,
    mut v___y_4877_: *mut leanh::LeanObject,
    mut v___y_4878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4880_: u8 = 0;
    let mut v___x_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4880_ = lean_nat_dec_le(v_endIdx_4870_, v_i_4872_);
                if v___x_4880_ == 0 {
                    v___x_4881_ = l_Lean_instInhabitedExpr;
                    v___x_4882_ = lean_array_get_borrowed(v___x_4881_, v_args_4869_, v_i_4872_);
                    leanh::lean_inc(v___x_4882_);
                    v___x_4883_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_b_4871_, v___x_4882_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
                    if leanh::lean_obj_tag(v___x_4883_) == 0 {
                        v_a_4884_ = leanh::lean_ctor_get(v___x_4883_, 0);
                        leanh::lean_inc(v_a_4884_);
                        leanh::lean_dec_ref_known(v___x_4883_, 1);
                        v___x_4885_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4886_ = lean_nat_add(v_i_4872_, v___x_4885_);
                        leanh::lean_dec(v_i_4872_);
                        v_b_4871_ = v_a_4884_;
                        v_i_4872_ = v___x_4886_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_4872_);
                        return v___x_4883_;
                    }
                } else {
                    leanh::lean_dec(v_i_4872_);
                    v___x_4888_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4888_, 0, v_b_4871_);
                    return v___x_4888_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg___boxed(
    mut v_args_4889_: *mut leanh::LeanObject,
    mut v_endIdx_4890_: *mut leanh::LeanObject,
    mut v_b_4891_: *mut leanh::LeanObject,
    mut v_i_4892_: *mut leanh::LeanObject,
    mut v___y_4893_: *mut leanh::LeanObject,
    mut v___y_4894_: *mut leanh::LeanObject,
    mut v___y_4895_: *mut leanh::LeanObject,
    mut v___y_4896_: *mut leanh::LeanObject,
    mut v___y_4897_: *mut leanh::LeanObject,
    mut v___y_4898_: *mut leanh::LeanObject,
    mut v___y_4899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4900_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_4889_, v_endIdx_4890_, v_b_4891_, v_i_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
    leanh::lean_dec(v___y_4898_);
    leanh::lean_dec_ref(v___y_4897_);
    leanh::lean_dec(v___y_4896_);
    leanh::lean_dec_ref(v___y_4895_);
    leanh::lean_dec(v___y_4894_);
    leanh::lean_dec_ref(v___y_4893_);
    leanh::lean_dec(v_endIdx_4890_);
    leanh::lean_dec_ref(v_args_4889_);
    return v_res_4900_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(
    mut v_f_4901_: *mut leanh::LeanObject,
    mut v_args_4902_: *mut leanh::LeanObject,
    mut v___y_4903_: *mut leanh::LeanObject,
    mut v___y_4904_: *mut leanh::LeanObject,
    mut v___y_4905_: *mut leanh::LeanObject,
    mut v___y_4906_: *mut leanh::LeanObject,
    mut v___y_4907_: *mut leanh::LeanObject,
    mut v___y_4908_: *mut leanh::LeanObject,
    mut v___y_4909_: *mut leanh::LeanObject,
    mut v___y_4910_: *mut leanh::LeanObject,
    mut v___y_4911_: *mut leanh::LeanObject,
    mut v___y_4912_: *mut leanh::LeanObject,
    mut v___y_4913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4915_ = leanh::lean_unsigned_to_nat(0);
    v___x_4916_ = lean_array_get_size(v_args_4902_);
    v___x_4917_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_4902_, v___x_4916_, v_f_4901_, v___x_4915_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_);
    return v___x_4917_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1___boxed(
    mut v_f_4918_: *mut leanh::LeanObject,
    mut v_args_4919_: *mut leanh::LeanObject,
    mut v___y_4920_: *mut leanh::LeanObject,
    mut v___y_4921_: *mut leanh::LeanObject,
    mut v___y_4922_: *mut leanh::LeanObject,
    mut v___y_4923_: *mut leanh::LeanObject,
    mut v___y_4924_: *mut leanh::LeanObject,
    mut v___y_4925_: *mut leanh::LeanObject,
    mut v___y_4926_: *mut leanh::LeanObject,
    mut v___y_4927_: *mut leanh::LeanObject,
    mut v___y_4928_: *mut leanh::LeanObject,
    mut v___y_4929_: *mut leanh::LeanObject,
    mut v___y_4930_: *mut leanh::LeanObject,
    mut v___y_4931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4932_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_f_4918_, v_args_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
    leanh::lean_dec(v___y_4930_);
    leanh::lean_dec_ref(v___y_4929_);
    leanh::lean_dec(v___y_4928_);
    leanh::lean_dec_ref(v___y_4927_);
    leanh::lean_dec(v___y_4926_);
    leanh::lean_dec_ref(v___y_4925_);
    leanh::lean_dec(v___y_4924_);
    leanh::lean_dec_ref(v___y_4923_);
    leanh::lean_dec(v___y_4922_);
    leanh::lean_dec(v___y_4921_);
    leanh::lean_dec_ref(v___y_4920_);
    leanh::lean_dec_ref(v_args_4919_);
    return v_res_4932_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(
    mut v_f_4933_: *mut leanh::LeanObject,
    mut v_a_u2081_4934_: *mut leanh::LeanObject,
    mut v_a_u2082_4935_: *mut leanh::LeanObject,
    mut v_a_u2083_4936_: *mut leanh::LeanObject,
    mut v_a_u2084_4937_: *mut leanh::LeanObject,
    mut v___y_4938_: *mut leanh::LeanObject,
    mut v___y_4939_: *mut leanh::LeanObject,
    mut v___y_4940_: *mut leanh::LeanObject,
    mut v___y_4941_: *mut leanh::LeanObject,
    mut v___y_4942_: *mut leanh::LeanObject,
    mut v___y_4943_: *mut leanh::LeanObject,
    mut v___y_4944_: *mut leanh::LeanObject,
    mut v___y_4945_: *mut leanh::LeanObject,
    mut v___y_4946_: *mut leanh::LeanObject,
    mut v___y_4947_: *mut leanh::LeanObject,
    mut v___y_4948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4950_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_f_4933_, v_a_u2081_4934_, v_a_u2082_4935_, v_a_u2083_4936_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
    if leanh::lean_obj_tag(v___x_4950_) == 0 {
        let mut v_a_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4951_ = leanh::lean_ctor_get(v___x_4950_, 0);
        leanh::lean_inc(v_a_4951_);
        leanh::lean_dec_ref_known(v___x_4950_, 1);
        v___x_4952_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_4951_, v_a_u2084_4937_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
        return v___x_4952_;
    } else {
        leanh::lean_dec_ref(v_a_u2084_4937_);
        return v___x_4950_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_4953_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_a_u2081_4954_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_a_u2082_4955_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_a_u2083_4956_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_u2084_4957_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_4958_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4959_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4960_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4961_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4962_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4963_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4964_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4965_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4966_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4967_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4968_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4969_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4970_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_f_4953_, v_a_u2081_4954_, v_a_u2082_4955_, v_a_u2083_4956_, v_a_u2084_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
    leanh::lean_dec(v___y_4968_);
    leanh::lean_dec_ref(v___y_4967_);
    leanh::lean_dec(v___y_4966_);
    leanh::lean_dec_ref(v___y_4965_);
    leanh::lean_dec(v___y_4964_);
    leanh::lean_dec_ref(v___y_4963_);
    leanh::lean_dec(v___y_4962_);
    leanh::lean_dec_ref(v___y_4961_);
    leanh::lean_dec(v___y_4960_);
    leanh::lean_dec(v___y_4959_);
    leanh::lean_dec_ref(v___y_4958_);
    return v_res_4970_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(
    mut v_f_4971_: *mut leanh::LeanObject,
    mut v_a_u2081_4972_: *mut leanh::LeanObject,
    mut v_a_u2082_4973_: *mut leanh::LeanObject,
    mut v_a_u2083_4974_: *mut leanh::LeanObject,
    mut v_a_u2084_4975_: *mut leanh::LeanObject,
    mut v_a_u2085_4976_: *mut leanh::LeanObject,
    mut v___y_4977_: *mut leanh::LeanObject,
    mut v___y_4978_: *mut leanh::LeanObject,
    mut v___y_4979_: *mut leanh::LeanObject,
    mut v___y_4980_: *mut leanh::LeanObject,
    mut v___y_4981_: *mut leanh::LeanObject,
    mut v___y_4982_: *mut leanh::LeanObject,
    mut v___y_4983_: *mut leanh::LeanObject,
    mut v___y_4984_: *mut leanh::LeanObject,
    mut v___y_4985_: *mut leanh::LeanObject,
    mut v___y_4986_: *mut leanh::LeanObject,
    mut v___y_4987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4989_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_f_4971_, v_a_u2081_4972_, v_a_u2082_4973_, v_a_u2083_4974_, v_a_u2084_4975_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
    if leanh::lean_obj_tag(v___x_4989_) == 0 {
        let mut v_a_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4990_ = leanh::lean_ctor_get(v___x_4989_, 0);
        leanh::lean_inc(v_a_4990_);
        leanh::lean_dec_ref_known(v___x_4989_, 1);
        v___x_4991_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_4990_, v_a_u2085_4976_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
        return v___x_4991_;
    } else {
        leanh::lean_dec_ref(v_a_u2085_4976_);
        return v___x_4989_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_4992_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_a_u2081_4993_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_a_u2082_4994_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_a_u2083_4995_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_u2084_4996_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_a_u2085_4997_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4998_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4999_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5000_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5001_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_5002_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5003_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5004_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5005_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5006_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5007_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5008_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5009_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5010_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_f_4992_, v_a_u2081_4993_, v_a_u2082_4994_, v_a_u2083_4995_, v_a_u2084_4996_, v_a_u2085_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
    leanh::lean_dec(v___y_5008_);
    leanh::lean_dec_ref(v___y_5007_);
    leanh::lean_dec(v___y_5006_);
    leanh::lean_dec_ref(v___y_5005_);
    leanh::lean_dec(v___y_5004_);
    leanh::lean_dec_ref(v___y_5003_);
    leanh::lean_dec(v___y_5002_);
    leanh::lean_dec_ref(v___y_5001_);
    leanh::lean_dec(v___y_5000_);
    leanh::lean_dec(v___y_4999_);
    leanh::lean_dec_ref(v___y_4998_);
    return v_res_5010_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(
    mut v_goal_5011_: *mut leanh::LeanObject,
    mut v_head_5012_: *mut leanh::LeanObject,
    mut v_H_5013_: *mut leanh::LeanObject,
    mut v_00_u03c3s_5014_: *mut leanh::LeanObject,
    mut v_ent_5015_: *mut leanh::LeanObject,
    mut v_args_5016_: *mut leanh::LeanObject,
    mut v_wpConst_5017_: *mut leanh::LeanObject,
    mut v_m_5018_: *mut leanh::LeanObject,
    mut v_ps_5019_: *mut leanh::LeanObject,
    mut v_instWP_5020_: *mut leanh::LeanObject,
    mut v_00_u03b1_5021_: *mut leanh::LeanObject,
    mut v_e_x27_5022_: *mut leanh::LeanObject,
    mut v_a_5023_: *mut leanh::LeanObject,
    mut v_a_5024_: *mut leanh::LeanObject,
    mut v_a_5025_: *mut leanh::LeanObject,
    mut v_a_5026_: *mut leanh::LeanObject,
    mut v_a_5027_: *mut leanh::LeanObject,
    mut v_a_5028_: *mut leanh::LeanObject,
    mut v_a_5029_: *mut leanh::LeanObject,
    mut v_a_5030_: *mut leanh::LeanObject,
    mut v_a_5031_: *mut leanh::LeanObject,
    mut v_a_5032_: *mut leanh::LeanObject,
    mut v_a_5033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5047_: u8 = 0;
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5051_: u8 = 0;
    let mut v_a_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5055_: u8 = 0;
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut v_a_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5035_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_wpConst_5017_, v_m_5018_, v_ps_5019_, v_instWP_5020_, v_00_u03b1_5021_, v_e_x27_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
                if leanh::lean_obj_tag(v___x_5035_) == 0 {
                    v_a_5036_ = leanh::lean_ctor_get(v___x_5035_, 0);
                    leanh::lean_inc(v_a_5036_);
                    leanh::lean_dec_ref_known(v___x_5035_, 1);
                    v___x_5037_ = leanh::lean_unsigned_to_nat(2);
                    v___x_5038_ = lean_array_set(v_args_5016_, v___x_5037_, v_a_5036_);
                    v___x_5039_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_head_5012_, v___x_5038_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
                    leanh::lean_dec_ref(v___x_5038_);
                    if leanh::lean_obj_tag(v___x_5039_) == 0 {
                        v_a_5040_ = leanh::lean_ctor_get(v___x_5039_, 0);
                        leanh::lean_inc(v_a_5040_);
                        leanh::lean_dec_ref_known(v___x_5039_, 1);
                        v___x_5041_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_5015_, v_00_u03c3s_5014_, v_H_5013_, v_a_5040_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
                        if leanh::lean_obj_tag(v___x_5041_) == 0 {
                            v_a_5042_ = leanh::lean_ctor_get(v___x_5041_, 0);
                            leanh::lean_inc(v_a_5042_);
                            leanh::lean_dec_ref_known(v___x_5041_, 1);
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
                            leanh::lean_dec(v_goal_5011_);
                            v_a_5044_ = leanh::lean_ctor_get(v___x_5041_, 0);
                            v_isSharedCheck_5051_ =
                                (!leanh::lean_is_exclusive(v___x_5041_)) as u8;
                            if v_isSharedCheck_5051_ == 0 {
                                v___x_5046_ = v___x_5041_;
                                v_isShared_5047_ = v_isSharedCheck_5051_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5044_);
                                leanh::lean_dec(v___x_5041_);
                                v___x_5046_ = leanh::lean_box(0);
                                v_isShared_5047_ = v_isSharedCheck_5051_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_ent_5015_);
                        leanh::lean_dec_ref(v_00_u03c3s_5014_);
                        leanh::lean_dec_ref(v_H_5013_);
                        leanh::lean_dec(v_goal_5011_);
                        v_a_5052_ = leanh::lean_ctor_get(v___x_5039_, 0);
                        v_isSharedCheck_5059_ =
                            (!leanh::lean_is_exclusive(v___x_5039_)) as u8;
                        if v_isSharedCheck_5059_ == 0 {
                            v___x_5054_ = v___x_5039_;
                            v_isShared_5055_ = v_isSharedCheck_5059_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5052_);
                            leanh::lean_dec(v___x_5039_);
                            v___x_5054_ = leanh::lean_box(0);
                            v_isShared_5055_ = v_isSharedCheck_5059_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_args_5016_);
                    leanh::lean_dec_ref(v_ent_5015_);
                    leanh::lean_dec_ref(v_00_u03c3s_5014_);
                    leanh::lean_dec_ref(v_H_5013_);
                    leanh::lean_dec_ref(v_head_5012_);
                    leanh::lean_dec(v_goal_5011_);
                    v_a_5060_ = leanh::lean_ctor_get(v___x_5035_, 0);
                    v_isSharedCheck_5067_ = (!leanh::lean_is_exclusive(v___x_5035_)) as u8;
                    if v_isSharedCheck_5067_ == 0 {
                        v___x_5062_ = v___x_5035_;
                        v_isShared_5063_ = v_isSharedCheck_5067_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5060_);
                        leanh::lean_dec(v___x_5035_);
                        v___x_5062_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5050_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
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
                    v_reuseFailAlloc_5058_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
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
                    v_reuseFailAlloc_5066_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_goal_5068_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_head_5069_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_H_5070_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_5071_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_ent_5072_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_args_5073_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_wpConst_5074_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_m_5075_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_ps_5076_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_instWP_5077_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_00_u03b1_5078_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_e_x27_5079_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_5080_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_5081_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_5082_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_5083_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_5084_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_5085_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_5086_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_5087_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_a_5088_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_a_5089_: *mut leanh::LeanObject = *_args.add(21);
    let mut v_a_5090_: *mut leanh::LeanObject = *_args.add(22);
    let mut v_a_5091_: *mut leanh::LeanObject = *_args.add(23);
    let mut v_res_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5092_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_5068_, v_head_5069_, v_H_5070_, v_00_u03c3s_5071_, v_ent_5072_, v_args_5073_, v_wpConst_5074_, v_m_5075_, v_ps_5076_, v_instWP_5077_, v_00_u03b1_5078_, v_e_x27_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_);
    leanh::lean_dec(v_a_5090_);
    leanh::lean_dec_ref(v_a_5089_);
    leanh::lean_dec(v_a_5088_);
    leanh::lean_dec_ref(v_a_5087_);
    leanh::lean_dec(v_a_5086_);
    leanh::lean_dec_ref(v_a_5085_);
    leanh::lean_dec(v_a_5084_);
    leanh::lean_dec_ref(v_a_5083_);
    leanh::lean_dec(v_a_5082_);
    leanh::lean_dec(v_a_5081_);
    leanh::lean_dec_ref(v_a_5080_);
    return v_res_5092_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2(
    mut v_args_5093_: *mut leanh::LeanObject,
    mut v_endIdx_5094_: *mut leanh::LeanObject,
    mut v_b_5095_: *mut leanh::LeanObject,
    mut v_i_5096_: *mut leanh::LeanObject,
    mut v___y_5097_: *mut leanh::LeanObject,
    mut v___y_5098_: *mut leanh::LeanObject,
    mut v___y_5099_: *mut leanh::LeanObject,
    mut v___y_5100_: *mut leanh::LeanObject,
    mut v___y_5101_: *mut leanh::LeanObject,
    mut v___y_5102_: *mut leanh::LeanObject,
    mut v___y_5103_: *mut leanh::LeanObject,
    mut v___y_5104_: *mut leanh::LeanObject,
    mut v___y_5105_: *mut leanh::LeanObject,
    mut v___y_5106_: *mut leanh::LeanObject,
    mut v___y_5107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5109_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_5093_, v_endIdx_5094_, v_b_5095_, v_i_5096_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
    return v___x_5109_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___boxed(
    mut v_args_5110_: *mut leanh::LeanObject,
    mut v_endIdx_5111_: *mut leanh::LeanObject,
    mut v_b_5112_: *mut leanh::LeanObject,
    mut v_i_5113_: *mut leanh::LeanObject,
    mut v___y_5114_: *mut leanh::LeanObject,
    mut v___y_5115_: *mut leanh::LeanObject,
    mut v___y_5116_: *mut leanh::LeanObject,
    mut v___y_5117_: *mut leanh::LeanObject,
    mut v___y_5118_: *mut leanh::LeanObject,
    mut v___y_5119_: *mut leanh::LeanObject,
    mut v___y_5120_: *mut leanh::LeanObject,
    mut v___y_5121_: *mut leanh::LeanObject,
    mut v___y_5122_: *mut leanh::LeanObject,
    mut v___y_5123_: *mut leanh::LeanObject,
    mut v___y_5124_: *mut leanh::LeanObject,
    mut v___y_5125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5126_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2(v_args_5110_, v_endIdx_5111_, v_b_5112_, v_i_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
    leanh::lean_dec(v___y_5124_);
    leanh::lean_dec_ref(v___y_5123_);
    leanh::lean_dec(v___y_5122_);
    leanh::lean_dec_ref(v___y_5121_);
    leanh::lean_dec(v___y_5120_);
    leanh::lean_dec_ref(v___y_5119_);
    leanh::lean_dec(v___y_5118_);
    leanh::lean_dec_ref(v___y_5117_);
    leanh::lean_dec(v___y_5116_);
    leanh::lean_dec(v___y_5115_);
    leanh::lean_dec_ref(v___y_5114_);
    leanh::lean_dec(v_endIdx_5111_);
    leanh::lean_dec_ref(v_args_5110_);
    return v_res_5126_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(
    mut v_revArgs_5127_: *mut leanh::LeanObject,
    mut v_start_5128_: *mut leanh::LeanObject,
    mut v_b_5129_: *mut leanh::LeanObject,
    mut v_i_5130_: *mut leanh::LeanObject,
    mut v___y_5131_: *mut leanh::LeanObject,
    mut v___y_5132_: *mut leanh::LeanObject,
    mut v___y_5133_: *mut leanh::LeanObject,
    mut v___y_5134_: *mut leanh::LeanObject,
    mut v___y_5135_: *mut leanh::LeanObject,
    mut v___y_5136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5138_: u8 = 0;
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5138_ = lean_nat_dec_le(v_i_5130_, v_start_5128_);
                if v___x_5138_ == 0 {
                    v___x_5139_ = leanh::lean_unsigned_to_nat(1);
                    v_i_5140_ = lean_nat_sub(v_i_5130_, v___x_5139_);
                    leanh::lean_dec(v_i_5130_);
                    v___x_5141_ = l_Lean_instInhabitedExpr;
                    v___x_5142_ = lean_array_get_borrowed(v___x_5141_, v_revArgs_5127_, v_i_5140_);
                    leanh::lean_inc(v___x_5142_);
                    v___x_5143_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_b_5129_, v___x_5142_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
                    if leanh::lean_obj_tag(v___x_5143_) == 0 {
                        v_a_5144_ = leanh::lean_ctor_get(v___x_5143_, 0);
                        leanh::lean_inc(v_a_5144_);
                        leanh::lean_dec_ref_known(v___x_5143_, 1);
                        v_b_5129_ = v_a_5144_;
                        v_i_5130_ = v_i_5140_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_5140_);
                        return v___x_5143_;
                    }
                } else {
                    leanh::lean_dec(v_i_5130_);
                    v___x_5146_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5146_, 0, v_b_5129_);
                    return v___x_5146_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg___boxed(
    mut v_revArgs_5147_: *mut leanh::LeanObject,
    mut v_start_5148_: *mut leanh::LeanObject,
    mut v_b_5149_: *mut leanh::LeanObject,
    mut v_i_5150_: *mut leanh::LeanObject,
    mut v___y_5151_: *mut leanh::LeanObject,
    mut v___y_5152_: *mut leanh::LeanObject,
    mut v___y_5153_: *mut leanh::LeanObject,
    mut v___y_5154_: *mut leanh::LeanObject,
    mut v___y_5155_: *mut leanh::LeanObject,
    mut v___y_5156_: *mut leanh::LeanObject,
    mut v___y_5157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5158_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_5147_, v_start_5148_, v_b_5149_, v_i_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_);
    leanh::lean_dec(v___y_5156_);
    leanh::lean_dec_ref(v___y_5155_);
    leanh::lean_dec(v___y_5154_);
    leanh::lean_dec_ref(v___y_5153_);
    leanh::lean_dec(v___y_5152_);
    leanh::lean_dec_ref(v___y_5151_);
    leanh::lean_dec(v_start_5148_);
    leanh::lean_dec_ref(v_revArgs_5147_);
    return v_res_5158_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(
    mut v_f_5159_: *mut leanh::LeanObject,
    mut v_revArgs_5160_: *mut leanh::LeanObject,
    mut v___y_5161_: *mut leanh::LeanObject,
    mut v___y_5162_: *mut leanh::LeanObject,
    mut v___y_5163_: *mut leanh::LeanObject,
    mut v___y_5164_: *mut leanh::LeanObject,
    mut v___y_5165_: *mut leanh::LeanObject,
    mut v___y_5166_: *mut leanh::LeanObject,
    mut v___y_5167_: *mut leanh::LeanObject,
    mut v___y_5168_: *mut leanh::LeanObject,
    mut v___y_5169_: *mut leanh::LeanObject,
    mut v___y_5170_: *mut leanh::LeanObject,
    mut v___y_5171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5173_ = leanh::lean_unsigned_to_nat(0);
    v___x_5174_ = lean_array_get_size(v_revArgs_5160_);
    v___x_5175_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_5160_, v___x_5173_, v_f_5159_, v___x_5174_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_);
    return v___x_5175_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0___boxed(
    mut v_f_5176_: *mut leanh::LeanObject,
    mut v_revArgs_5177_: *mut leanh::LeanObject,
    mut v___y_5178_: *mut leanh::LeanObject,
    mut v___y_5179_: *mut leanh::LeanObject,
    mut v___y_5180_: *mut leanh::LeanObject,
    mut v___y_5181_: *mut leanh::LeanObject,
    mut v___y_5182_: *mut leanh::LeanObject,
    mut v___y_5183_: *mut leanh::LeanObject,
    mut v___y_5184_: *mut leanh::LeanObject,
    mut v___y_5185_: *mut leanh::LeanObject,
    mut v___y_5186_: *mut leanh::LeanObject,
    mut v___y_5187_: *mut leanh::LeanObject,
    mut v___y_5188_: *mut leanh::LeanObject,
    mut v___y_5189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5190_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(v_f_5176_, v_revArgs_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_);
    leanh::lean_dec(v___y_5188_);
    leanh::lean_dec_ref(v___y_5187_);
    leanh::lean_dec(v___y_5186_);
    leanh::lean_dec_ref(v___y_5185_);
    leanh::lean_dec(v___y_5184_);
    leanh::lean_dec_ref(v___y_5183_);
    leanh::lean_dec(v___y_5182_);
    leanh::lean_dec_ref(v___y_5181_);
    leanh::lean_dec(v___y_5180_);
    leanh::lean_dec(v___y_5179_);
    leanh::lean_dec_ref(v___y_5178_);
    leanh::lean_dec_ref(v_revArgs_5177_);
    return v_res_5190_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5192_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0;
    v___x_5193_ = l_Lean_stringToMessageData(v___x_5192_);
    return v___x_5193_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(
    mut v_goal_5194_: *mut leanh::LeanObject,
    mut v_head_5195_: *mut leanh::LeanObject,
    mut v_H_5196_: *mut leanh::LeanObject,
    mut v_00_u03c3s_5197_: *mut leanh::LeanObject,
    mut v_ent_5198_: *mut leanh::LeanObject,
    mut v_args_5199_: *mut leanh::LeanObject,
    mut v_wpConst_5200_: *mut leanh::LeanObject,
    mut v_m_5201_: *mut leanh::LeanObject,
    mut v_ps_5202_: *mut leanh::LeanObject,
    mut v_instWP_5203_: *mut leanh::LeanObject,
    mut v_00_u03b1_5204_: *mut leanh::LeanObject,
    mut v_e_5205_: *mut leanh::LeanObject,
    mut v_f_5206_: *mut leanh::LeanObject,
    mut v_a_5207_: *mut leanh::LeanObject,
    mut v_a_5208_: *mut leanh::LeanObject,
    mut v_a_5209_: *mut leanh::LeanObject,
    mut v_a_5210_: *mut leanh::LeanObject,
    mut v_a_5211_: *mut leanh::LeanObject,
    mut v_a_5212_: *mut leanh::LeanObject,
    mut v_a_5213_: *mut leanh::LeanObject,
    mut v_a_5214_: *mut leanh::LeanObject,
    mut v_a_5215_: *mut leanh::LeanObject,
    mut v_a_5216_: *mut leanh::LeanObject,
    mut v_a_5217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_5223_: u8 = 0;
    let mut v___y_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5254_: u8 = 0;
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5259_: u8 = 0;
    let mut v_a_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5263_: u8 = 0;
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut v_a_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5271_: u8 = 0;
    let mut v___x_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut v_a_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut v_a_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5287_: u8 = 0;
    let mut v___x_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5291_: u8 = 0;
    let mut v_a_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5295_: u8 = 0;
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5299_: u8 = 0;
    let mut v_options_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5301_: u8 = 0;
    let mut v_inheritedTraceOptions_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: u8 = 0;
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5313_: u8 = 0;
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_f_5206_) == 8 {
                    v_declName_5219_ = leanh::lean_ctor_get(v_f_5206_, 0);
                    leanh::lean_inc(v_declName_5219_);
                    v_type_5220_ = leanh::lean_ctor_get(v_f_5206_, 1);
                    leanh::lean_inc_ref(v_type_5220_);
                    v_value_5221_ = leanh::lean_ctor_get(v_f_5206_, 2);
                    leanh::lean_inc_ref(v_value_5221_);
                    v_body_5222_ = leanh::lean_ctor_get(v_f_5206_, 3);
                    leanh::lean_inc_ref(v_body_5222_);
                    v_nondep_5223_ = leanh::lean_ctor_get_uint8(
                        v_f_5206_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_dec_ref_known(v_f_5206_, 4);
                    v_options_5300_ = leanh::lean_ctor_get(v_a_5216_, 2);
                    v_hasTrace_5301_ = leanh::lean_ctor_get_uint8(
                        v_options_5300_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                        v_inheritedTraceOptions_5302_ = leanh::lean_ctor_get(v_a_5216_, 13);
                        v_cls_5303_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                        v___x_5304_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
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
                            v___x_5306_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1);
                            leanh::lean_inc(v_declName_5219_);
                            v___x_5307_ = l_Lean_MessageData_ofName(v_declName_5219_);
                            v___x_5308_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5308_, 0, v___x_5306_);
                            leanh::lean_ctor_set(v___x_5308_, 1, v___x_5307_);
                            v___x_5309_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_5303_, v___x_5308_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
                            if leanh::lean_obj_tag(v___x_5309_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5309_, 1);
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
                                leanh::lean_dec_ref(v_body_5222_);
                                leanh::lean_dec_ref(v_value_5221_);
                                leanh::lean_dec_ref(v_type_5220_);
                                leanh::lean_dec(v_declName_5219_);
                                leanh::lean_dec_ref(v_e_5205_);
                                leanh::lean_dec_ref(v_00_u03b1_5204_);
                                leanh::lean_dec_ref(v_instWP_5203_);
                                leanh::lean_dec_ref(v_ps_5202_);
                                leanh::lean_dec_ref(v_m_5201_);
                                leanh::lean_dec_ref(v_wpConst_5200_);
                                leanh::lean_dec_ref(v_args_5199_);
                                leanh::lean_dec_ref(v_ent_5198_);
                                leanh::lean_dec_ref(v_00_u03c3s_5197_);
                                leanh::lean_dec_ref(v_H_5196_);
                                leanh::lean_dec_ref(v_head_5195_);
                                leanh::lean_dec(v_goal_5194_);
                                v_a_5310_ = leanh::lean_ctor_get(v___x_5309_, 0);
                                v_isSharedCheck_5317_ =
                                    (!leanh::lean_is_exclusive(v___x_5309_)) as u8;
                                if v_isSharedCheck_5317_ == 0 {
                                    v___x_5312_ = v___x_5309_;
                                    v_isShared_5313_ = v_isSharedCheck_5317_;
                                    state = 14;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5310_);
                                    leanh::lean_dec(v___x_5309_);
                                    v___x_5312_ = leanh::lean_box(0);
                                    v_isShared_5313_ = v_isSharedCheck_5317_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_f_5206_);
                    leanh::lean_dec_ref(v_e_5205_);
                    leanh::lean_dec_ref(v_00_u03b1_5204_);
                    leanh::lean_dec_ref(v_instWP_5203_);
                    leanh::lean_dec_ref(v_ps_5202_);
                    leanh::lean_dec_ref(v_m_5201_);
                    leanh::lean_dec_ref(v_wpConst_5200_);
                    leanh::lean_dec_ref(v_args_5199_);
                    leanh::lean_dec_ref(v_ent_5198_);
                    leanh::lean_dec_ref(v_00_u03c3s_5197_);
                    leanh::lean_dec_ref(v_H_5196_);
                    leanh::lean_dec_ref(v_head_5195_);
                    leanh::lean_dec(v_goal_5194_);
                    v___x_5318_ = leanh::lean_box(0);
                    v___x_5319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5319_, 0, v___x_5318_);
                    return v___x_5319_;
                }
            }
            1 => {
                v___x_5236_ = l_Lean_Expr_getAppNumArgs(v_e_5205_);
                v___x_5237_ = lean_mk_empty_array_with_capacity(v___x_5236_);
                leanh::lean_dec(v___x_5236_);
                v___x_5238_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_5205_, v___x_5237_);
                v___x_5239_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(v_body_5222_, v___x_5238_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
                leanh::lean_dec_ref(v___x_5238_);
                if leanh::lean_obj_tag(v___x_5239_) == 0 {
                    v_a_5240_ = leanh::lean_ctor_get(v___x_5239_, 0);
                    leanh::lean_inc(v_a_5240_);
                    leanh::lean_dec_ref_known(v___x_5239_, 1);
                    v___x_5241_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_wpConst_5200_, v_m_5201_, v_ps_5202_, v_instWP_5203_, v_00_u03b1_5204_, v_a_5240_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
                    if leanh::lean_obj_tag(v___x_5241_) == 0 {
                        v_a_5242_ = leanh::lean_ctor_get(v___x_5241_, 0);
                        leanh::lean_inc(v_a_5242_);
                        leanh::lean_dec_ref_known(v___x_5241_, 1);
                        v___x_5243_ = leanh::lean_unsigned_to_nat(2);
                        v___x_5244_ = lean_array_set(v_args_5199_, v___x_5243_, v_a_5242_);
                        v___x_5245_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_head_5195_, v___x_5244_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
                        leanh::lean_dec_ref(v___x_5244_);
                        if leanh::lean_obj_tag(v___x_5245_) == 0 {
                            v_a_5246_ = leanh::lean_ctor_get(v___x_5245_, 0);
                            leanh::lean_inc(v_a_5246_);
                            leanh::lean_dec_ref_known(v___x_5245_, 1);
                            v___x_5247_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_5198_, v_00_u03c3s_5197_, v_H_5196_, v_a_5246_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
                            if leanh::lean_obj_tag(v___x_5247_) == 0 {
                                v_a_5248_ = leanh::lean_ctor_get(v___x_5247_, 0);
                                leanh::lean_inc(v_a_5248_);
                                leanh::lean_dec_ref_known(v___x_5247_, 1);
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
                                if leanh::lean_obj_tag(v___x_5250_) == 0 {
                                    v_a_5251_ = leanh::lean_ctor_get(v___x_5250_, 0);
                                    v_isSharedCheck_5259_ =
                                        (!leanh::lean_is_exclusive(v___x_5250_)) as u8;
                                    if v_isSharedCheck_5259_ == 0 {
                                        v___x_5253_ = v___x_5250_;
                                        v_isShared_5254_ = v_isSharedCheck_5259_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5251_);
                                        leanh::lean_dec(v___x_5250_);
                                        v___x_5253_ = leanh::lean_box(0);
                                        v_isShared_5254_ = v_isSharedCheck_5259_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_a_5260_ = leanh::lean_ctor_get(v___x_5250_, 0);
                                    v_isSharedCheck_5267_ =
                                        (!leanh::lean_is_exclusive(v___x_5250_)) as u8;
                                    if v_isSharedCheck_5267_ == 0 {
                                        v___x_5262_ = v___x_5250_;
                                        v_isShared_5263_ = v_isSharedCheck_5267_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5260_);
                                        leanh::lean_dec(v___x_5250_);
                                        v___x_5262_ = leanh::lean_box(0);
                                        v_isShared_5263_ = v_isSharedCheck_5267_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_value_5221_);
                                leanh::lean_dec_ref(v_type_5220_);
                                leanh::lean_dec(v_declName_5219_);
                                leanh::lean_dec(v_goal_5194_);
                                v_a_5268_ = leanh::lean_ctor_get(v___x_5247_, 0);
                                v_isSharedCheck_5275_ =
                                    (!leanh::lean_is_exclusive(v___x_5247_)) as u8;
                                if v_isSharedCheck_5275_ == 0 {
                                    v___x_5270_ = v___x_5247_;
                                    v_isShared_5271_ = v_isSharedCheck_5275_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5268_);
                                    leanh::lean_dec(v___x_5247_);
                                    v___x_5270_ = leanh::lean_box(0);
                                    v_isShared_5271_ = v_isSharedCheck_5275_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_value_5221_);
                            leanh::lean_dec_ref(v_type_5220_);
                            leanh::lean_dec(v_declName_5219_);
                            leanh::lean_dec_ref(v_ent_5198_);
                            leanh::lean_dec_ref(v_00_u03c3s_5197_);
                            leanh::lean_dec_ref(v_H_5196_);
                            leanh::lean_dec(v_goal_5194_);
                            v_a_5276_ = leanh::lean_ctor_get(v___x_5245_, 0);
                            v_isSharedCheck_5283_ =
                                (!leanh::lean_is_exclusive(v___x_5245_)) as u8;
                            if v_isSharedCheck_5283_ == 0 {
                                v___x_5278_ = v___x_5245_;
                                v_isShared_5279_ = v_isSharedCheck_5283_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5276_);
                                leanh::lean_dec(v___x_5245_);
                                v___x_5278_ = leanh::lean_box(0);
                                v_isShared_5279_ = v_isSharedCheck_5283_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_value_5221_);
                        leanh::lean_dec_ref(v_type_5220_);
                        leanh::lean_dec(v_declName_5219_);
                        leanh::lean_dec_ref(v_args_5199_);
                        leanh::lean_dec_ref(v_ent_5198_);
                        leanh::lean_dec_ref(v_00_u03c3s_5197_);
                        leanh::lean_dec_ref(v_H_5196_);
                        leanh::lean_dec_ref(v_head_5195_);
                        leanh::lean_dec(v_goal_5194_);
                        v_a_5284_ = leanh::lean_ctor_get(v___x_5241_, 0);
                        v_isSharedCheck_5291_ =
                            (!leanh::lean_is_exclusive(v___x_5241_)) as u8;
                        if v_isSharedCheck_5291_ == 0 {
                            v___x_5286_ = v___x_5241_;
                            v_isShared_5287_ = v_isSharedCheck_5291_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5284_);
                            leanh::lean_dec(v___x_5241_);
                            v___x_5286_ = leanh::lean_box(0);
                            v_isShared_5287_ = v_isSharedCheck_5291_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_value_5221_);
                    leanh::lean_dec_ref(v_type_5220_);
                    leanh::lean_dec(v_declName_5219_);
                    leanh::lean_dec_ref(v_00_u03b1_5204_);
                    leanh::lean_dec_ref(v_instWP_5203_);
                    leanh::lean_dec_ref(v_ps_5202_);
                    leanh::lean_dec_ref(v_m_5201_);
                    leanh::lean_dec_ref(v_wpConst_5200_);
                    leanh::lean_dec_ref(v_args_5199_);
                    leanh::lean_dec_ref(v_ent_5198_);
                    leanh::lean_dec_ref(v_00_u03c3s_5197_);
                    leanh::lean_dec_ref(v_H_5196_);
                    leanh::lean_dec_ref(v_head_5195_);
                    leanh::lean_dec(v_goal_5194_);
                    v_a_5292_ = leanh::lean_ctor_get(v___x_5239_, 0);
                    v_isSharedCheck_5299_ = (!leanh::lean_is_exclusive(v___x_5239_)) as u8;
                    if v_isSharedCheck_5299_ == 0 {
                        v___x_5294_ = v___x_5239_;
                        v_isShared_5295_ = v_isSharedCheck_5299_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5292_);
                        leanh::lean_dec(v___x_5239_);
                        v___x_5294_ = leanh::lean_box(0);
                        v_isShared_5295_ = v_isSharedCheck_5299_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5255_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5255_, 0, v_a_5251_);
                if v_isShared_5254_ == 0 {
                    leanh::lean_ctor_set(v___x_5253_, 0, v___x_5255_);
                    v___x_5257_ = v___x_5253_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5258_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5258_, 0, v___x_5255_);
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
                    v_reuseFailAlloc_5266_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
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
                    v_reuseFailAlloc_5274_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
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
                    v_reuseFailAlloc_5282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
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
                    v_reuseFailAlloc_5290_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
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
                    v_reuseFailAlloc_5298_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_a_5292_);
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
                    v_reuseFailAlloc_5316_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_goal_5320_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_head_5321_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_H_5322_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_5323_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_ent_5324_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_args_5325_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_wpConst_5326_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_m_5327_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_ps_5328_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_instWP_5329_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_00_u03b1_5330_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_e_5331_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_f_5332_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_5333_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_5334_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_5335_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_5336_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_5337_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_5338_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_5339_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_a_5340_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_a_5341_: *mut leanh::LeanObject = *_args.add(21);
    let mut v_a_5342_: *mut leanh::LeanObject = *_args.add(22);
    let mut v_a_5343_: *mut leanh::LeanObject = *_args.add(23);
    let mut v_a_5344_: *mut leanh::LeanObject = *_args.add(24);
    let mut v_res_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5345_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(v_goal_5320_, v_head_5321_, v_H_5322_, v_00_u03c3s_5323_, v_ent_5324_, v_args_5325_, v_wpConst_5326_, v_m_5327_, v_ps_5328_, v_instWP_5329_, v_00_u03b1_5330_, v_e_5331_, v_f_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_);
    leanh::lean_dec(v_a_5343_);
    leanh::lean_dec_ref(v_a_5342_);
    leanh::lean_dec(v_a_5341_);
    leanh::lean_dec_ref(v_a_5340_);
    leanh::lean_dec(v_a_5339_);
    leanh::lean_dec_ref(v_a_5338_);
    leanh::lean_dec(v_a_5337_);
    leanh::lean_dec_ref(v_a_5336_);
    leanh::lean_dec(v_a_5335_);
    leanh::lean_dec(v_a_5334_);
    leanh::lean_dec_ref(v_a_5333_);
    return v_res_5345_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0(
    mut v_revArgs_5346_: *mut leanh::LeanObject,
    mut v_start_5347_: *mut leanh::LeanObject,
    mut v_b_5348_: *mut leanh::LeanObject,
    mut v_i_5349_: *mut leanh::LeanObject,
    mut v___y_5350_: *mut leanh::LeanObject,
    mut v___y_5351_: *mut leanh::LeanObject,
    mut v___y_5352_: *mut leanh::LeanObject,
    mut v___y_5353_: *mut leanh::LeanObject,
    mut v___y_5354_: *mut leanh::LeanObject,
    mut v___y_5355_: *mut leanh::LeanObject,
    mut v___y_5356_: *mut leanh::LeanObject,
    mut v___y_5357_: *mut leanh::LeanObject,
    mut v___y_5358_: *mut leanh::LeanObject,
    mut v___y_5359_: *mut leanh::LeanObject,
    mut v___y_5360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5362_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_5346_, v_start_5347_, v_b_5348_, v_i_5349_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_);
    return v___x_5362_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___boxed(
    mut v_revArgs_5363_: *mut leanh::LeanObject,
    mut v_start_5364_: *mut leanh::LeanObject,
    mut v_b_5365_: *mut leanh::LeanObject,
    mut v_i_5366_: *mut leanh::LeanObject,
    mut v___y_5367_: *mut leanh::LeanObject,
    mut v___y_5368_: *mut leanh::LeanObject,
    mut v___y_5369_: *mut leanh::LeanObject,
    mut v___y_5370_: *mut leanh::LeanObject,
    mut v___y_5371_: *mut leanh::LeanObject,
    mut v___y_5372_: *mut leanh::LeanObject,
    mut v___y_5373_: *mut leanh::LeanObject,
    mut v___y_5374_: *mut leanh::LeanObject,
    mut v___y_5375_: *mut leanh::LeanObject,
    mut v___y_5376_: *mut leanh::LeanObject,
    mut v___y_5377_: *mut leanh::LeanObject,
    mut v___y_5378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5379_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0(v_revArgs_5363_, v_start_5364_, v_b_5365_, v_i_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
    leanh::lean_dec(v___y_5377_);
    leanh::lean_dec_ref(v___y_5376_);
    leanh::lean_dec(v___y_5375_);
    leanh::lean_dec_ref(v___y_5374_);
    leanh::lean_dec(v___y_5373_);
    leanh::lean_dec_ref(v___y_5372_);
    leanh::lean_dec(v___y_5371_);
    leanh::lean_dec_ref(v___y_5370_);
    leanh::lean_dec(v___y_5369_);
    leanh::lean_dec(v___y_5368_);
    leanh::lean_dec_ref(v___y_5367_);
    leanh::lean_dec(v_start_5364_);
    leanh::lean_dec_ref(v_revArgs_5363_);
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
-> *mut leanh::LeanObject {
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5383_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1;
    v___x_5384_ = l_Lean_stringToMessageData(v___x_5383_);
    return v___x_5384_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5386_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3;
    v___x_5387_ = l_Lean_stringToMessageData(v___x_5386_);
    return v___x_5387_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(
    mut v_goal_5388_: *mut leanh::LeanObject,
    mut v_head_5389_: *mut leanh::LeanObject,
    mut v_H_5390_: *mut leanh::LeanObject,
    mut v_00_u03c3s_5391_: *mut leanh::LeanObject,
    mut v_ent_5392_: *mut leanh::LeanObject,
    mut v_args_5393_: *mut leanh::LeanObject,
    mut v_wpConst_5394_: *mut leanh::LeanObject,
    mut v_m_5395_: *mut leanh::LeanObject,
    mut v_ps_5396_: *mut leanh::LeanObject,
    mut v_instWP_5397_: *mut leanh::LeanObject,
    mut v_00_u03b1_5398_: *mut leanh::LeanObject,
    mut v_e_5399_: *mut leanh::LeanObject,
    mut v_excessArgs_5400_: *mut leanh::LeanObject,
    mut v_a_5401_: *mut leanh::LeanObject,
    mut v_a_5402_: *mut leanh::LeanObject,
    mut v_a_5403_: *mut leanh::LeanObject,
    mut v_a_5404_: *mut leanh::LeanObject,
    mut v_a_5405_: *mut leanh::LeanObject,
    mut v_a_5406_: *mut leanh::LeanObject,
    mut v_a_5407_: *mut leanh::LeanObject,
    mut v_a_5408_: *mut leanh::LeanObject,
    mut v_a_5409_: *mut leanh::LeanObject,
    mut v_a_5410_: *mut leanh::LeanObject,
    mut v_a_5411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5417_: u8 = 0;
    let mut v_val_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5421_: u8 = 0;
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5443_: u8 = 0;
    let mut v_trackZetaDelta_5444_: u8 = 0;
    let mut v_zetaDeltaSet_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5451_: u8 = 0;
    let mut v_inTypeClassResolution_5452_: u8 = 0;
    let mut v_cacheInferType_5453_: u8 = 0;
    let mut v___x_5454_: u8 = 0;
    let mut v_config_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: u64 = 0;
    let mut v___x_5458_: u64 = 0;
    let mut v___x_5459_: u64 = 0;
    let mut v___x_5460_: u64 = 0;
    let mut v___x_5461_: u64 = 0;
    let mut v_key_5462_: u64 = 0;
    let mut v___x_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5470_: u8 = 0;
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5477_: u8 = 0;
    let mut v___x_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5486_: u8 = 0;
    let mut v_a_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5490_: u8 = 0;
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_a_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5498_: u8 = 0;
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5502_: u8 = 0;
    let mut v_isSharedCheck_5503_: u8 = 0;
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5515_: u8 = 0;
    let mut v_mvarIds_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5519_: u8 = 0;
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5526_: u8 = 0;
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5530_: u8 = 0;
    let mut v_a_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5534_: u8 = 0;
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5538_: u8 = 0;
    let mut v_reuseFailAlloc_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5543_: u8 = 0;
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5547_: u8 = 0;
    let mut v_a_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5551_: u8 = 0;
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5555_: u8 = 0;
    let mut v_reuseFailAlloc_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5557_: u8 = 0;
    let mut v_isSharedCheck_5558_: u8 = 0;
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5563_: u8 = 0;
    let mut v_a_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5567_: u8 = 0;
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_5399_);
                v___x_5413_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(
                    v_e_5399_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_,
                );
                if leanh::lean_obj_tag(v___x_5413_) == 0 {
                    v_a_5414_ = leanh::lean_ctor_get(v___x_5413_, 0);
                    v_isSharedCheck_5563_ = (!leanh::lean_is_exclusive(v___x_5413_)) as u8;
                    if v_isSharedCheck_5563_ == 0 {
                        v___x_5416_ = v___x_5413_;
                        v_isShared_5417_ = v_isSharedCheck_5563_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5414_);
                        leanh::lean_dec(v___x_5413_);
                        v___x_5416_ = leanh::lean_box(0);
                        v_isShared_5417_ = v_isSharedCheck_5563_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_excessArgs_5400_);
                    leanh::lean_dec_ref(v_e_5399_);
                    leanh::lean_dec_ref(v_00_u03b1_5398_);
                    leanh::lean_dec_ref(v_instWP_5397_);
                    leanh::lean_dec_ref(v_ps_5396_);
                    leanh::lean_dec_ref(v_m_5395_);
                    leanh::lean_dec_ref(v_wpConst_5394_);
                    leanh::lean_dec_ref(v_args_5393_);
                    leanh::lean_dec_ref(v_ent_5392_);
                    leanh::lean_dec_ref(v_00_u03c3s_5391_);
                    leanh::lean_dec_ref(v_H_5390_);
                    leanh::lean_dec_ref(v_head_5389_);
                    leanh::lean_dec(v_goal_5388_);
                    v_a_5564_ = leanh::lean_ctor_get(v___x_5413_, 0);
                    v_isSharedCheck_5571_ = (!leanh::lean_is_exclusive(v___x_5413_)) as u8;
                    if v_isSharedCheck_5571_ == 0 {
                        v___x_5566_ = v___x_5413_;
                        v_isShared_5567_ = v_isSharedCheck_5571_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5564_);
                        leanh::lean_dec(v___x_5413_);
                        v___x_5566_ = leanh::lean_box(0);
                        v_isShared_5567_ = v_isSharedCheck_5571_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5414_) == 1 {
                    leanh::lean_del_object(v___x_5416_);
                    v_val_5418_ = leanh::lean_ctor_get(v_a_5414_, 0);
                    v_isSharedCheck_5558_ = (!leanh::lean_is_exclusive(v_a_5414_)) as u8;
                    if v_isSharedCheck_5558_ == 0 {
                        v___x_5420_ = v_a_5414_;
                        v_isShared_5421_ = v_isSharedCheck_5558_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5418_);
                        leanh::lean_dec(v_a_5414_);
                        v___x_5420_ = leanh::lean_box(0);
                        v_isShared_5421_ = v_isSharedCheck_5558_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5414_);
                    leanh::lean_dec_ref(v_excessArgs_5400_);
                    leanh::lean_dec_ref(v_e_5399_);
                    leanh::lean_dec_ref(v_00_u03b1_5398_);
                    leanh::lean_dec_ref(v_instWP_5397_);
                    leanh::lean_dec_ref(v_ps_5396_);
                    leanh::lean_dec_ref(v_m_5395_);
                    leanh::lean_dec_ref(v_wpConst_5394_);
                    leanh::lean_dec_ref(v_args_5393_);
                    leanh::lean_dec_ref(v_ent_5392_);
                    leanh::lean_dec_ref(v_00_u03c3s_5391_);
                    leanh::lean_dec_ref(v_H_5390_);
                    leanh::lean_dec_ref(v_head_5389_);
                    leanh::lean_dec(v_goal_5388_);
                    v___x_5559_ = leanh::lean_box(0);
                    if v_isShared_5417_ == 0 {
                        leanh::lean_ctor_set(v___x_5416_, 0, v___x_5559_);
                        v___x_5561_ = v___x_5416_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_5562_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5562_, 0, v___x_5559_);
                        v___x_5561_ = v_reuseFailAlloc_5562_;
                        state = 24;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5422_ = l_Lean_Meta_Context_config(v_a_5408_);
                v_foApprox_5423_ = leanh::lean_ctor_get_uint8(v___x_5422_, 0 as u32);
                v_ctxApprox_5424_ = leanh::lean_ctor_get_uint8(v___x_5422_, 1 as u32);
                v_quasiPatternApprox_5425_ =
                    leanh::lean_ctor_get_uint8(v___x_5422_, 2 as u32);
                v_constApprox_5426_ = leanh::lean_ctor_get_uint8(v___x_5422_, 3 as u32);
                v_isDefEqStuckEx_5427_ = leanh::lean_ctor_get_uint8(v___x_5422_, 4 as u32);
                v_unificationHints_5428_ = leanh::lean_ctor_get_uint8(v___x_5422_, 5 as u32);
                v_proofIrrelevance_5429_ = leanh::lean_ctor_get_uint8(v___x_5422_, 6 as u32);
                v_assignSyntheticOpaque_5430_ =
                    leanh::lean_ctor_get_uint8(v___x_5422_, 7 as u32);
                v_offsetCnstrs_5431_ = leanh::lean_ctor_get_uint8(v___x_5422_, 8 as u32);
                v_etaStruct_5432_ = leanh::lean_ctor_get_uint8(v___x_5422_, 10 as u32);
                v_univApprox_5433_ = leanh::lean_ctor_get_uint8(v___x_5422_, 11 as u32);
                v_iota_5434_ = leanh::lean_ctor_get_uint8(v___x_5422_, 12 as u32);
                v_beta_5435_ = leanh::lean_ctor_get_uint8(v___x_5422_, 13 as u32);
                v_proj_5436_ = leanh::lean_ctor_get_uint8(v___x_5422_, 14 as u32);
                v_zeta_5437_ = leanh::lean_ctor_get_uint8(v___x_5422_, 15 as u32);
                v_zetaDelta_5438_ = leanh::lean_ctor_get_uint8(v___x_5422_, 16 as u32);
                v_zetaUnused_5439_ = leanh::lean_ctor_get_uint8(v___x_5422_, 17 as u32);
                v_zetaHave_5440_ = leanh::lean_ctor_get_uint8(v___x_5422_, 18 as u32);
                v_isSharedCheck_5557_ = (!leanh::lean_is_exclusive(v___x_5422_)) as u8;
                if v_isSharedCheck_5557_ == 0 {
                    v___x_5442_ = v___x_5422_;
                    v_isShared_5443_ = v_isSharedCheck_5557_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_5422_);
                    v___x_5442_ = leanh::lean_box(0);
                    v_isShared_5443_ = v_isSharedCheck_5557_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_trackZetaDelta_5444_ = leanh::lean_ctor_get_uint8(
                    v_a_5408_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5445_ = leanh::lean_ctor_get(v_a_5408_, 1);
                v_lctx_5446_ = leanh::lean_ctor_get(v_a_5408_, 2);
                v_localInstances_5447_ = leanh::lean_ctor_get(v_a_5408_, 3);
                v_defEqCtx_x3f_5448_ = leanh::lean_ctor_get(v_a_5408_, 4);
                v_synthPendingDepth_5449_ = leanh::lean_ctor_get(v_a_5408_, 5);
                v_canUnfold_x3f_5450_ = leanh::lean_ctor_get(v_a_5408_, 6);
                v_univApprox_5451_ = leanh::lean_ctor_get_uint8(
                    v_a_5408_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5452_ = leanh::lean_ctor_get_uint8(
                    v_a_5408_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5453_ = leanh::lean_ctor_get_uint8(
                    v_a_5408_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5454_ = 2;
                if v_isShared_5443_ == 0 {
                    v_config_5456_ = v___x_5442_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5556_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        0 as u32,
                        v_foApprox_5423_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        1 as u32,
                        v_ctxApprox_5424_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        2 as u32,
                        v_quasiPatternApprox_5425_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        3 as u32,
                        v_constApprox_5426_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        4 as u32,
                        v_isDefEqStuckEx_5427_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        5 as u32,
                        v_unificationHints_5428_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        6 as u32,
                        v_proofIrrelevance_5429_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        7 as u32,
                        v_assignSyntheticOpaque_5430_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        8 as u32,
                        v_offsetCnstrs_5431_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        10 as u32,
                        v_etaStruct_5432_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        11 as u32,
                        v_univApprox_5433_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        12 as u32,
                        v_iota_5434_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        13 as u32,
                        v_beta_5435_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        14 as u32,
                        v_proj_5436_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        15 as u32,
                        v_zeta_5437_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        16 as u32,
                        v_zetaDelta_5438_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5556_,
                        17 as u32,
                        v_zetaUnused_5439_,
                    );
                    leanh::lean_ctor_set_uint8(
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
                leanh::lean_ctor_set_uint8(v_config_5456_, 9 as u32, v___x_5454_);
                v___x_5457_ = l_Lean_Meta_Context_configKey(v_a_5408_);
                v___x_5458_ = 3u64;
                v___x_5459_ = lean_uint64_shift_right(v___x_5457_, v___x_5458_);
                v___x_5460_ = lean_uint64_shift_left(v___x_5459_, v___x_5458_);
                v___x_5461_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0);
                v_key_5462_ = lean_uint64_lor(v___x_5460_, v___x_5461_);
                v___x_5463_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_5463_, 0, v_config_5456_);
                leanh::lean_ctor_set_uint64(
                    v___x_5463_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_5462_,
                );
                leanh::lean_inc(v_canUnfold_x3f_5450_);
                leanh::lean_inc(v_synthPendingDepth_5449_);
                leanh::lean_inc(v_defEqCtx_x3f_5448_);
                leanh::lean_inc_ref(v_localInstances_5447_);
                leanh::lean_inc_ref(v_lctx_5446_);
                leanh::lean_inc(v_zetaDeltaSet_5445_);
                v___x_5464_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_5464_, 0, v___x_5463_);
                leanh::lean_ctor_set(v___x_5464_, 1, v_zetaDeltaSet_5445_);
                leanh::lean_ctor_set(v___x_5464_, 2, v_lctx_5446_);
                leanh::lean_ctor_set(v___x_5464_, 3, v_localInstances_5447_);
                leanh::lean_ctor_set(v___x_5464_, 4, v_defEqCtx_x3f_5448_);
                leanh::lean_ctor_set(v___x_5464_, 5, v_synthPendingDepth_5449_);
                leanh::lean_ctor_set(v___x_5464_, 6, v_canUnfold_x3f_5450_);
                leanh::lean_ctor_set_uint8(
                    v___x_5464_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5444_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5464_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5451_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5464_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5452_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5464_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5453_,
                );
                v___x_5465_ = l_Lean_Meta_reduceRecMatcher_x3f(
                    v_e_5399_,
                    v___x_5464_,
                    v_a_5409_,
                    v_a_5410_,
                    v_a_5411_,
                );
                leanh::lean_dec_ref_known(v___x_5464_, 7);
                if leanh::lean_obj_tag(v___x_5465_) == 0 {
                    v_a_5466_ = leanh::lean_ctor_get(v___x_5465_, 0);
                    leanh::lean_inc(v_a_5466_);
                    leanh::lean_dec_ref_known(v___x_5465_, 1);
                    if leanh::lean_obj_tag(v_a_5466_) == 1 {
                        leanh::lean_del_object(v___x_5420_);
                        leanh::lean_dec(v_val_5418_);
                        leanh::lean_dec_ref(v_excessArgs_5400_);
                        leanh::lean_dec_ref(v_e_5399_);
                        v_val_5467_ = leanh::lean_ctor_get(v_a_5466_, 0);
                        v_isSharedCheck_5503_ = (!leanh::lean_is_exclusive(v_a_5466_)) as u8;
                        if v_isSharedCheck_5503_ == 0 {
                            v___x_5469_ = v_a_5466_;
                            v_isShared_5470_ = v_isSharedCheck_5503_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_5467_);
                            leanh::lean_dec(v_a_5466_);
                            v___x_5469_ = leanh::lean_box(0);
                            v_isShared_5470_ = v_isSharedCheck_5503_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_5466_);
                        leanh::lean_dec_ref(v_00_u03b1_5398_);
                        leanh::lean_dec_ref(v_wpConst_5394_);
                        leanh::lean_dec_ref(v_args_5393_);
                        leanh::lean_dec_ref(v_ent_5392_);
                        leanh::lean_dec_ref(v_H_5390_);
                        leanh::lean_dec_ref(v_head_5389_);
                        v___x_5504_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(v_val_5418_, v_m_5395_, v_00_u03c3s_5391_, v_ps_5396_, v_instWP_5397_, v_excessArgs_5400_, v_a_5402_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
                        if leanh::lean_obj_tag(v___x_5504_) == 0 {
                            v_a_5505_ = leanh::lean_ctor_get(v___x_5504_, 0);
                            leanh::lean_inc(v_a_5505_);
                            leanh::lean_dec_ref_known(v___x_5504_, 1);
                            v___x_5506_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2);
                            v___x_5507_ = l_Lean_indentExpr(v_e_5399_);
                            leanh::lean_inc_ref(v___x_5507_);
                            v___x_5508_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5508_, 0, v___x_5506_);
                            leanh::lean_ctor_set(v___x_5508_, 1, v___x_5507_);
                            if v_isShared_5421_ == 0 {
                                leanh::lean_ctor_set(v___x_5420_, 0, v___x_5508_);
                                v___x_5510_ = v___x_5420_;
                                state = 13;
                                continue;
                            } else {
                                v_reuseFailAlloc_5539_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5508_);
                                v___x_5510_ = v_reuseFailAlloc_5539_;
                                state = 13;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_5420_);
                            leanh::lean_dec_ref(v_e_5399_);
                            leanh::lean_dec(v_goal_5388_);
                            v_a_5540_ = leanh::lean_ctor_get(v___x_5504_, 0);
                            v_isSharedCheck_5547_ =
                                (!leanh::lean_is_exclusive(v___x_5504_)) as u8;
                            if v_isSharedCheck_5547_ == 0 {
                                v___x_5542_ = v___x_5504_;
                                v_isShared_5543_ = v_isSharedCheck_5547_;
                                state = 20;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5540_);
                                leanh::lean_dec(v___x_5504_);
                                v___x_5542_ = leanh::lean_box(0);
                                v_isShared_5543_ = v_isSharedCheck_5547_;
                                state = 20;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5420_);
                    leanh::lean_dec(v_val_5418_);
                    leanh::lean_dec_ref(v_excessArgs_5400_);
                    leanh::lean_dec_ref(v_e_5399_);
                    leanh::lean_dec_ref(v_00_u03b1_5398_);
                    leanh::lean_dec_ref(v_instWP_5397_);
                    leanh::lean_dec_ref(v_ps_5396_);
                    leanh::lean_dec_ref(v_m_5395_);
                    leanh::lean_dec_ref(v_wpConst_5394_);
                    leanh::lean_dec_ref(v_args_5393_);
                    leanh::lean_dec_ref(v_ent_5392_);
                    leanh::lean_dec_ref(v_00_u03c3s_5391_);
                    leanh::lean_dec_ref(v_H_5390_);
                    leanh::lean_dec_ref(v_head_5389_);
                    leanh::lean_dec(v_goal_5388_);
                    v_a_5548_ = leanh::lean_ctor_get(v___x_5465_, 0);
                    v_isSharedCheck_5555_ = (!leanh::lean_is_exclusive(v___x_5465_)) as u8;
                    if v_isSharedCheck_5555_ == 0 {
                        v___x_5550_ = v___x_5465_;
                        v_isShared_5551_ = v_isSharedCheck_5555_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5548_);
                        leanh::lean_dec(v___x_5465_);
                        v___x_5550_ = leanh::lean_box(0);
                        v_isShared_5551_ = v_isSharedCheck_5555_;
                        state = 22;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5471_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_5467_, v_a_5407_);
                if leanh::lean_obj_tag(v___x_5471_) == 0 {
                    v_a_5472_ = leanh::lean_ctor_get(v___x_5471_, 0);
                    leanh::lean_inc(v_a_5472_);
                    leanh::lean_dec_ref_known(v___x_5471_, 1);
                    v___x_5473_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_5388_, v_head_5389_, v_H_5390_, v_00_u03c3s_5391_, v_ent_5392_, v_args_5393_, v_wpConst_5394_, v_m_5395_, v_ps_5396_, v_instWP_5397_, v_00_u03b1_5398_, v_a_5472_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
                    if leanh::lean_obj_tag(v___x_5473_) == 0 {
                        v_a_5474_ = leanh::lean_ctor_get(v___x_5473_, 0);
                        v_isSharedCheck_5486_ =
                            (!leanh::lean_is_exclusive(v___x_5473_)) as u8;
                        if v_isSharedCheck_5486_ == 0 {
                            v___x_5476_ = v___x_5473_;
                            v_isShared_5477_ = v_isSharedCheck_5486_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5474_);
                            leanh::lean_dec(v___x_5473_);
                            v___x_5476_ = leanh::lean_box(0);
                            v_isShared_5477_ = v_isSharedCheck_5486_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5469_);
                        v_a_5487_ = leanh::lean_ctor_get(v___x_5473_, 0);
                        v_isSharedCheck_5494_ =
                            (!leanh::lean_is_exclusive(v___x_5473_)) as u8;
                        if v_isSharedCheck_5494_ == 0 {
                            v___x_5489_ = v___x_5473_;
                            v_isShared_5490_ = v_isSharedCheck_5494_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5487_);
                            leanh::lean_dec(v___x_5473_);
                            v___x_5489_ = leanh::lean_box(0);
                            v_isShared_5490_ = v_isSharedCheck_5494_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5469_);
                    leanh::lean_dec_ref(v_00_u03b1_5398_);
                    leanh::lean_dec_ref(v_instWP_5397_);
                    leanh::lean_dec_ref(v_ps_5396_);
                    leanh::lean_dec_ref(v_m_5395_);
                    leanh::lean_dec_ref(v_wpConst_5394_);
                    leanh::lean_dec_ref(v_args_5393_);
                    leanh::lean_dec_ref(v_ent_5392_);
                    leanh::lean_dec_ref(v_00_u03c3s_5391_);
                    leanh::lean_dec_ref(v_H_5390_);
                    leanh::lean_dec_ref(v_head_5389_);
                    leanh::lean_dec(v_goal_5388_);
                    v_a_5495_ = leanh::lean_ctor_get(v___x_5471_, 0);
                    v_isSharedCheck_5502_ = (!leanh::lean_is_exclusive(v___x_5471_)) as u8;
                    if v_isSharedCheck_5502_ == 0 {
                        v___x_5497_ = v___x_5471_;
                        v_isShared_5498_ = v_isSharedCheck_5502_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5495_);
                        leanh::lean_dec(v___x_5471_);
                        v___x_5497_ = leanh::lean_box(0);
                        v_isShared_5498_ = v_isSharedCheck_5502_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5478_ = leanh::lean_box(0);
                v___x_5479_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5479_, 0, v_a_5474_);
                leanh::lean_ctor_set(v___x_5479_, 1, v___x_5478_);
                if v_isShared_5470_ == 0 {
                    leanh::lean_ctor_set(v___x_5469_, 0, v___x_5479_);
                    v___x_5481_ = v___x_5469_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5485_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5485_, 0, v___x_5479_);
                    v___x_5481_ = v_reuseFailAlloc_5485_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5477_ == 0 {
                    leanh::lean_ctor_set(v___x_5476_, 0, v___x_5481_);
                    v___x_5483_ = v___x_5476_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5484_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5481_);
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
                    v_reuseFailAlloc_5493_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
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
                    v_reuseFailAlloc_5501_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5495_);
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
                if leanh::lean_obj_tag(v___x_5511_) == 0 {
                    v_a_5512_ = leanh::lean_ctor_get(v___x_5511_, 0);
                    v_isSharedCheck_5530_ = (!leanh::lean_is_exclusive(v___x_5511_)) as u8;
                    if v_isSharedCheck_5530_ == 0 {
                        v___x_5514_ = v___x_5511_;
                        v_isShared_5515_ = v_isSharedCheck_5530_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5512_);
                        leanh::lean_dec(v___x_5511_);
                        v___x_5514_ = leanh::lean_box(0);
                        v_isShared_5515_ = v_isSharedCheck_5530_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5507_);
                    v_a_5531_ = leanh::lean_ctor_get(v___x_5511_, 0);
                    v_isSharedCheck_5538_ = (!leanh::lean_is_exclusive(v___x_5511_)) as u8;
                    if v_isSharedCheck_5538_ == 0 {
                        v___x_5533_ = v___x_5511_;
                        v_isShared_5534_ = v_isSharedCheck_5538_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5531_);
                        leanh::lean_dec(v___x_5511_);
                        v___x_5533_ = leanh::lean_box(0);
                        v_isShared_5534_ = v_isSharedCheck_5538_;
                        state = 18;
                        continue;
                    }
                }
            }
            14 => {
                if leanh::lean_obj_tag(v_a_5512_) == 1 {
                    leanh::lean_dec_ref(v___x_5507_);
                    v_mvarIds_5516_ = leanh::lean_ctor_get(v_a_5512_, 0);
                    v_isSharedCheck_5526_ = (!leanh::lean_is_exclusive(v_a_5512_)) as u8;
                    if v_isSharedCheck_5526_ == 0 {
                        v___x_5518_ = v_a_5512_;
                        v_isShared_5519_ = v_isSharedCheck_5526_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_mvarIds_5516_);
                        leanh::lean_dec(v_a_5512_);
                        v___x_5518_ = leanh::lean_box(0);
                        v_isShared_5519_ = v_isSharedCheck_5526_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5514_);
                    leanh::lean_dec(v_a_5512_);
                    v___x_5527_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4);
                    v___x_5528_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5528_, 0, v___x_5527_);
                    leanh::lean_ctor_set(v___x_5528_, 1, v___x_5507_);
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
                    v_reuseFailAlloc_5525_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_mvarIds_5516_);
                    v___x_5521_ = v_reuseFailAlloc_5525_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_5515_ == 0 {
                    leanh::lean_ctor_set(v___x_5514_, 0, v___x_5521_);
                    v___x_5523_ = v___x_5514_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5524_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5521_);
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
                    v_reuseFailAlloc_5537_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_a_5531_);
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
                    v_reuseFailAlloc_5546_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
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
                    v_reuseFailAlloc_5554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_a_5548_);
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
                    v_reuseFailAlloc_5570_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_a_5564_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_goal_5572_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_head_5573_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_H_5574_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_5575_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_ent_5576_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_args_5577_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_wpConst_5578_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_m_5579_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_ps_5580_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_instWP_5581_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_00_u03b1_5582_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_e_5583_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_excessArgs_5584_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_5585_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_5586_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_5587_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_5588_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_5589_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_5590_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_5591_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_a_5592_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_a_5593_: *mut leanh::LeanObject = *_args.add(21);
    let mut v_a_5594_: *mut leanh::LeanObject = *_args.add(22);
    let mut v_a_5595_: *mut leanh::LeanObject = *_args.add(23);
    let mut v_a_5596_: *mut leanh::LeanObject = *_args.add(24);
    let mut v_res_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5597_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(v_goal_5572_, v_head_5573_, v_H_5574_, v_00_u03c3s_5575_, v_ent_5576_, v_args_5577_, v_wpConst_5578_, v_m_5579_, v_ps_5580_, v_instWP_5581_, v_00_u03b1_5582_, v_e_5583_, v_excessArgs_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
    leanh::lean_dec(v_a_5595_);
    leanh::lean_dec_ref(v_a_5594_);
    leanh::lean_dec(v_a_5593_);
    leanh::lean_dec_ref(v_a_5592_);
    leanh::lean_dec(v_a_5591_);
    leanh::lean_dec_ref(v_a_5590_);
    leanh::lean_dec(v_a_5589_);
    leanh::lean_dec_ref(v_a_5588_);
    leanh::lean_dec(v_a_5587_);
    leanh::lean_dec(v_a_5586_);
    leanh::lean_dec_ref(v_a_5585_);
    return v_res_5597_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5599_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0;
    v___x_5600_ = l_Lean_stringToMessageData(v___x_5599_);
    return v___x_5600_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(
    mut v_goal_5601_: *mut leanh::LeanObject,
    mut v_head_5602_: *mut leanh::LeanObject,
    mut v_H_5603_: *mut leanh::LeanObject,
    mut v_00_u03c3s_5604_: *mut leanh::LeanObject,
    mut v_ent_5605_: *mut leanh::LeanObject,
    mut v_args_5606_: *mut leanh::LeanObject,
    mut v_wpConst_5607_: *mut leanh::LeanObject,
    mut v_m_5608_: *mut leanh::LeanObject,
    mut v_ps_5609_: *mut leanh::LeanObject,
    mut v_instWP_5610_: *mut leanh::LeanObject,
    mut v_00_u03b1_5611_: *mut leanh::LeanObject,
    mut v_e_5612_: *mut leanh::LeanObject,
    mut v_f_5613_: *mut leanh::LeanObject,
    mut v_a_5614_: *mut leanh::LeanObject,
    mut v_a_5615_: *mut leanh::LeanObject,
    mut v_a_5616_: *mut leanh::LeanObject,
    mut v_a_5617_: *mut leanh::LeanObject,
    mut v_a_5618_: *mut leanh::LeanObject,
    mut v_a_5619_: *mut leanh::LeanObject,
    mut v_a_5620_: *mut leanh::LeanObject,
    mut v_a_5621_: *mut leanh::LeanObject,
    mut v_a_5622_: *mut leanh::LeanObject,
    mut v_a_5623_: *mut leanh::LeanObject,
    mut v_a_5624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: u8 = 0;
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5633_: u8 = 0;
    let mut v_val_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5637_: u8 = 0;
    let mut v___y_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5660_: u8 = 0;
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v_a_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut v_a_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5679_: u8 = 0;
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5683_: u8 = 0;
    let mut v_options_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5685_: u8 = 0;
    let mut v_inheritedTraceOptions_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: u8 = 0;
    let mut v___x_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5703_: u8 = 0;
    let mut v_a_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5707_: u8 = 0;
    let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5711_: u8 = 0;
    let mut v_isSharedCheck_5712_: u8 = 0;
    let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5717_: u8 = 0;
    let mut v_a_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5725_: u8 = 0;
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5626_ = l_Lean_Expr_fvarId_x3f(v_f_5613_);
                if leanh::lean_obj_tag(v___x_5626_) == 1 {
                    v_val_5627_ = leanh::lean_ctor_get(v___x_5626_, 0);
                    leanh::lean_inc_n(v_val_5627_, 2);
                    leanh::lean_dec_ref_known(v___x_5626_, 1);
                    v___x_5628_ = 0;
                    v___x_5629_ = l_Lean_FVarId_getValue_x3f___redArg(
                        v_val_5627_,
                        v___x_5628_,
                        v_a_5621_,
                        v_a_5623_,
                        v_a_5624_,
                    );
                    if leanh::lean_obj_tag(v___x_5629_) == 0 {
                        v_a_5630_ = leanh::lean_ctor_get(v___x_5629_, 0);
                        v_isSharedCheck_5717_ =
                            (!leanh::lean_is_exclusive(v___x_5629_)) as u8;
                        if v_isSharedCheck_5717_ == 0 {
                            v___x_5632_ = v___x_5629_;
                            v_isShared_5633_ = v_isSharedCheck_5717_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5630_);
                            leanh::lean_dec(v___x_5629_);
                            v___x_5632_ = leanh::lean_box(0);
                            v_isShared_5633_ = v_isSharedCheck_5717_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5627_);
                        leanh::lean_dec_ref(v_e_5612_);
                        leanh::lean_dec_ref(v_00_u03b1_5611_);
                        leanh::lean_dec_ref(v_instWP_5610_);
                        leanh::lean_dec_ref(v_ps_5609_);
                        leanh::lean_dec_ref(v_m_5608_);
                        leanh::lean_dec_ref(v_wpConst_5607_);
                        leanh::lean_dec_ref(v_args_5606_);
                        leanh::lean_dec_ref(v_ent_5605_);
                        leanh::lean_dec_ref(v_00_u03c3s_5604_);
                        leanh::lean_dec_ref(v_H_5603_);
                        leanh::lean_dec_ref(v_head_5602_);
                        leanh::lean_dec(v_goal_5601_);
                        v_a_5718_ = leanh::lean_ctor_get(v___x_5629_, 0);
                        v_isSharedCheck_5725_ =
                            (!leanh::lean_is_exclusive(v___x_5629_)) as u8;
                        if v_isSharedCheck_5725_ == 0 {
                            v___x_5720_ = v___x_5629_;
                            v_isShared_5721_ = v_isSharedCheck_5725_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5718_);
                            leanh::lean_dec(v___x_5629_);
                            v___x_5720_ = leanh::lean_box(0);
                            v_isShared_5721_ = v_isSharedCheck_5725_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_5626_);
                    leanh::lean_dec_ref(v_e_5612_);
                    leanh::lean_dec_ref(v_00_u03b1_5611_);
                    leanh::lean_dec_ref(v_instWP_5610_);
                    leanh::lean_dec_ref(v_ps_5609_);
                    leanh::lean_dec_ref(v_m_5608_);
                    leanh::lean_dec_ref(v_wpConst_5607_);
                    leanh::lean_dec_ref(v_args_5606_);
                    leanh::lean_dec_ref(v_ent_5605_);
                    leanh::lean_dec_ref(v_00_u03c3s_5604_);
                    leanh::lean_dec_ref(v_H_5603_);
                    leanh::lean_dec_ref(v_head_5602_);
                    leanh::lean_dec(v_goal_5601_);
                    v___x_5726_ = leanh::lean_box(0);
                    v___x_5727_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5727_, 0, v___x_5726_);
                    return v___x_5727_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5630_) == 1 {
                    leanh::lean_del_object(v___x_5632_);
                    v_val_5634_ = leanh::lean_ctor_get(v_a_5630_, 0);
                    v_isSharedCheck_5712_ = (!leanh::lean_is_exclusive(v_a_5630_)) as u8;
                    if v_isSharedCheck_5712_ == 0 {
                        v___x_5636_ = v_a_5630_;
                        v_isShared_5637_ = v_isSharedCheck_5712_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5634_);
                        leanh::lean_dec(v_a_5630_);
                        v___x_5636_ = leanh::lean_box(0);
                        v_isShared_5637_ = v_isSharedCheck_5712_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5630_);
                    leanh::lean_dec(v_val_5627_);
                    leanh::lean_dec_ref(v_e_5612_);
                    leanh::lean_dec_ref(v_00_u03b1_5611_);
                    leanh::lean_dec_ref(v_instWP_5610_);
                    leanh::lean_dec_ref(v_ps_5609_);
                    leanh::lean_dec_ref(v_m_5608_);
                    leanh::lean_dec_ref(v_wpConst_5607_);
                    leanh::lean_dec_ref(v_args_5606_);
                    leanh::lean_dec_ref(v_ent_5605_);
                    leanh::lean_dec_ref(v_00_u03c3s_5604_);
                    leanh::lean_dec_ref(v_H_5603_);
                    leanh::lean_dec_ref(v_head_5602_);
                    leanh::lean_dec(v_goal_5601_);
                    v___x_5713_ = leanh::lean_box(0);
                    if v_isShared_5633_ == 0 {
                        leanh::lean_ctor_set(v___x_5632_, 0, v___x_5713_);
                        v___x_5715_ = v___x_5632_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_5716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 0, v___x_5713_);
                        v___x_5715_ = v_reuseFailAlloc_5716_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_options_5684_ = leanh::lean_ctor_get(v_a_5623_, 2);
                v_hasTrace_5685_ = leanh::lean_ctor_get_uint8(
                    v_options_5684_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5685_ == 0 {
                    leanh::lean_dec(v_val_5627_);
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
                    v_inheritedTraceOptions_5686_ = leanh::lean_ctor_get(v_a_5623_, 13);
                    v___x_5687_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                    v___x_5688_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
                    v___x_5689_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5686_,
                        v_options_5684_,
                        v___x_5688_,
                    );
                    if v___x_5689_ == 0 {
                        leanh::lean_dec(v_val_5627_);
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
                        if leanh::lean_obj_tag(v___x_5690_) == 0 {
                            v_a_5691_ = leanh::lean_ctor_get(v___x_5690_, 0);
                            leanh::lean_inc(v_a_5691_);
                            leanh::lean_dec_ref_known(v___x_5690_, 1);
                            v___x_5692_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1);
                            v___x_5693_ = l_Lean_MessageData_ofName(v_a_5691_);
                            v___x_5694_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5694_, 0, v___x_5692_);
                            leanh::lean_ctor_set(v___x_5694_, 1, v___x_5693_);
                            v___x_5695_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_5687_, v___x_5694_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_);
                            if leanh::lean_obj_tag(v___x_5695_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5695_, 1);
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
                                leanh::lean_del_object(v___x_5636_);
                                leanh::lean_dec(v_val_5634_);
                                leanh::lean_dec_ref(v_e_5612_);
                                leanh::lean_dec_ref(v_00_u03b1_5611_);
                                leanh::lean_dec_ref(v_instWP_5610_);
                                leanh::lean_dec_ref(v_ps_5609_);
                                leanh::lean_dec_ref(v_m_5608_);
                                leanh::lean_dec_ref(v_wpConst_5607_);
                                leanh::lean_dec_ref(v_args_5606_);
                                leanh::lean_dec_ref(v_ent_5605_);
                                leanh::lean_dec_ref(v_00_u03c3s_5604_);
                                leanh::lean_dec_ref(v_H_5603_);
                                leanh::lean_dec_ref(v_head_5602_);
                                leanh::lean_dec(v_goal_5601_);
                                v_a_5696_ = leanh::lean_ctor_get(v___x_5695_, 0);
                                v_isSharedCheck_5703_ =
                                    (!leanh::lean_is_exclusive(v___x_5695_)) as u8;
                                if v_isSharedCheck_5703_ == 0 {
                                    v___x_5698_ = v___x_5695_;
                                    v_isShared_5699_ = v_isSharedCheck_5703_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5696_);
                                    leanh::lean_dec(v___x_5695_);
                                    v___x_5698_ = leanh::lean_box(0);
                                    v_isShared_5699_ = v_isSharedCheck_5703_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_5636_);
                            leanh::lean_dec(v_val_5634_);
                            leanh::lean_dec_ref(v_e_5612_);
                            leanh::lean_dec_ref(v_00_u03b1_5611_);
                            leanh::lean_dec_ref(v_instWP_5610_);
                            leanh::lean_dec_ref(v_ps_5609_);
                            leanh::lean_dec_ref(v_m_5608_);
                            leanh::lean_dec_ref(v_wpConst_5607_);
                            leanh::lean_dec_ref(v_args_5606_);
                            leanh::lean_dec_ref(v_ent_5605_);
                            leanh::lean_dec_ref(v_00_u03c3s_5604_);
                            leanh::lean_dec_ref(v_H_5603_);
                            leanh::lean_dec_ref(v_head_5602_);
                            leanh::lean_dec(v_goal_5601_);
                            v_a_5704_ = leanh::lean_ctor_get(v___x_5690_, 0);
                            v_isSharedCheck_5711_ =
                                (!leanh::lean_is_exclusive(v___x_5690_)) as u8;
                            if v_isSharedCheck_5711_ == 0 {
                                v___x_5706_ = v___x_5690_;
                                v_isShared_5707_ = v_isSharedCheck_5711_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5704_);
                                leanh::lean_dec(v___x_5690_);
                                v___x_5706_ = leanh::lean_box(0);
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
                leanh::lean_dec(v___x_5650_);
                v___x_5652_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_5612_, v___x_5651_);
                v___x_5653_ =
                    l_Lean_Expr_betaRev(v_val_5634_, v___x_5652_, v___x_5628_, v___x_5628_);
                leanh::lean_dec_ref(v___x_5652_);
                v___x_5654_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_5653_, v___y_5645_);
                if leanh::lean_obj_tag(v___x_5654_) == 0 {
                    v_a_5655_ = leanh::lean_ctor_get(v___x_5654_, 0);
                    leanh::lean_inc(v_a_5655_);
                    leanh::lean_dec_ref_known(v___x_5654_, 1);
                    v___x_5656_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_5601_, v_head_5602_, v_H_5603_, v_00_u03c3s_5604_, v_ent_5605_, v_args_5606_, v_wpConst_5607_, v_m_5608_, v_ps_5609_, v_instWP_5610_, v_00_u03b1_5611_, v_a_5655_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
                    if leanh::lean_obj_tag(v___x_5656_) == 0 {
                        v_a_5657_ = leanh::lean_ctor_get(v___x_5656_, 0);
                        v_isSharedCheck_5667_ =
                            (!leanh::lean_is_exclusive(v___x_5656_)) as u8;
                        if v_isSharedCheck_5667_ == 0 {
                            v___x_5659_ = v___x_5656_;
                            v_isShared_5660_ = v_isSharedCheck_5667_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5657_);
                            leanh::lean_dec(v___x_5656_);
                            v___x_5659_ = leanh::lean_box(0);
                            v_isShared_5660_ = v_isSharedCheck_5667_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5636_);
                        v_a_5668_ = leanh::lean_ctor_get(v___x_5656_, 0);
                        v_isSharedCheck_5675_ =
                            (!leanh::lean_is_exclusive(v___x_5656_)) as u8;
                        if v_isSharedCheck_5675_ == 0 {
                            v___x_5670_ = v___x_5656_;
                            v_isShared_5671_ = v_isSharedCheck_5675_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5668_);
                            leanh::lean_dec(v___x_5656_);
                            v___x_5670_ = leanh::lean_box(0);
                            v_isShared_5671_ = v_isSharedCheck_5675_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5636_);
                    leanh::lean_dec_ref(v_00_u03b1_5611_);
                    leanh::lean_dec_ref(v_instWP_5610_);
                    leanh::lean_dec_ref(v_ps_5609_);
                    leanh::lean_dec_ref(v_m_5608_);
                    leanh::lean_dec_ref(v_wpConst_5607_);
                    leanh::lean_dec_ref(v_args_5606_);
                    leanh::lean_dec_ref(v_ent_5605_);
                    leanh::lean_dec_ref(v_00_u03c3s_5604_);
                    leanh::lean_dec_ref(v_H_5603_);
                    leanh::lean_dec_ref(v_head_5602_);
                    leanh::lean_dec(v_goal_5601_);
                    v_a_5676_ = leanh::lean_ctor_get(v___x_5654_, 0);
                    v_isSharedCheck_5683_ = (!leanh::lean_is_exclusive(v___x_5654_)) as u8;
                    if v_isSharedCheck_5683_ == 0 {
                        v___x_5678_ = v___x_5654_;
                        v_isShared_5679_ = v_isSharedCheck_5683_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5676_);
                        leanh::lean_dec(v___x_5654_);
                        v___x_5678_ = leanh::lean_box(0);
                        v_isShared_5679_ = v_isSharedCheck_5683_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5637_ == 0 {
                    leanh::lean_ctor_set(v___x_5636_, 0, v_a_5657_);
                    v___x_5662_ = v___x_5636_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5666_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_a_5657_);
                    v___x_5662_ = v_reuseFailAlloc_5666_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5660_ == 0 {
                    leanh::lean_ctor_set(v___x_5659_, 0, v___x_5662_);
                    v___x_5664_ = v___x_5659_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5665_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5665_, 0, v___x_5662_);
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
                    v_reuseFailAlloc_5674_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
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
                    v_reuseFailAlloc_5682_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_a_5676_);
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
                    v_reuseFailAlloc_5702_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5696_);
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
                    v_reuseFailAlloc_5710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5710_, 0, v_a_5704_);
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
                    v_reuseFailAlloc_5724_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5724_, 0, v_a_5718_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_goal_5728_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_head_5729_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_H_5730_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_5731_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_ent_5732_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_args_5733_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_wpConst_5734_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_m_5735_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_ps_5736_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_instWP_5737_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_00_u03b1_5738_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_e_5739_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_f_5740_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_5741_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_5742_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_5743_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_5744_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_5745_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_5746_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_5747_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_a_5748_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_a_5749_: *mut leanh::LeanObject = *_args.add(21);
    let mut v_a_5750_: *mut leanh::LeanObject = *_args.add(22);
    let mut v_a_5751_: *mut leanh::LeanObject = *_args.add(23);
    let mut v_a_5752_: *mut leanh::LeanObject = *_args.add(24);
    let mut v_res_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5753_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(v_goal_5728_, v_head_5729_, v_H_5730_, v_00_u03c3s_5731_, v_ent_5732_, v_args_5733_, v_wpConst_5734_, v_m_5735_, v_ps_5736_, v_instWP_5737_, v_00_u03b1_5738_, v_e_5739_, v_f_5740_, v_a_5741_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_);
    leanh::lean_dec(v_a_5751_);
    leanh::lean_dec_ref(v_a_5750_);
    leanh::lean_dec(v_a_5749_);
    leanh::lean_dec_ref(v_a_5748_);
    leanh::lean_dec(v_a_5747_);
    leanh::lean_dec_ref(v_a_5746_);
    leanh::lean_dec(v_a_5745_);
    leanh::lean_dec_ref(v_a_5744_);
    leanh::lean_dec(v_a_5743_);
    leanh::lean_dec(v_a_5742_);
    leanh::lean_dec_ref(v_a_5741_);
    leanh::lean_dec_ref(v_f_5740_);
    return v_res_5753_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceProg(
    mut v_goal_5754_: *mut leanh::LeanObject,
    mut v_head_5755_: *mut leanh::LeanObject,
    mut v_H_5756_: *mut leanh::LeanObject,
    mut v_00_u03c3s_5757_: *mut leanh::LeanObject,
    mut v_ent_5758_: *mut leanh::LeanObject,
    mut v_args_5759_: *mut leanh::LeanObject,
    mut v_wpConst_5760_: *mut leanh::LeanObject,
    mut v_m_5761_: *mut leanh::LeanObject,
    mut v_ps_5762_: *mut leanh::LeanObject,
    mut v_instWP_5763_: *mut leanh::LeanObject,
    mut v_00_u03b1_5764_: *mut leanh::LeanObject,
    mut v_e_5765_: *mut leanh::LeanObject,
    mut v_f_5766_: *mut leanh::LeanObject,
    mut v_a_5767_: *mut leanh::LeanObject,
    mut v_a_5768_: *mut leanh::LeanObject,
    mut v_a_5769_: *mut leanh::LeanObject,
    mut v_a_5770_: *mut leanh::LeanObject,
    mut v_a_5771_: *mut leanh::LeanObject,
    mut v_a_5772_: *mut leanh::LeanObject,
    mut v_a_5773_: *mut leanh::LeanObject,
    mut v_a_5774_: *mut leanh::LeanObject,
    mut v_a_5775_: *mut leanh::LeanObject,
    mut v_a_5776_: *mut leanh::LeanObject,
    mut v_a_5777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5783_: u8 = 0;
    let mut v_val_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5792_: u8 = 0;
    let mut v___x_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5799_: u8 = 0;
    let mut v_a_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5803_: u8 = 0;
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5807_: u8 = 0;
    let mut v_isSharedCheck_5808_: u8 = 0;
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5813_: u8 = 0;
    let mut v_a_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5817_: u8 = 0;
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5821_: u8 = 0;
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_f_5766_) == 11 {
                    v___x_5779_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(
                        v_e_5765_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_,
                    );
                    if leanh::lean_obj_tag(v___x_5779_) == 0 {
                        v_a_5780_ = leanh::lean_ctor_get(v___x_5779_, 0);
                        v_isSharedCheck_5813_ =
                            (!leanh::lean_is_exclusive(v___x_5779_)) as u8;
                        if v_isSharedCheck_5813_ == 0 {
                            v___x_5782_ = v___x_5779_;
                            v_isShared_5783_ = v_isSharedCheck_5813_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5780_);
                            leanh::lean_dec(v___x_5779_);
                            v___x_5782_ = leanh::lean_box(0);
                            v_isShared_5783_ = v_isSharedCheck_5813_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_00_u03b1_5764_);
                        leanh::lean_dec_ref(v_instWP_5763_);
                        leanh::lean_dec_ref(v_ps_5762_);
                        leanh::lean_dec_ref(v_m_5761_);
                        leanh::lean_dec_ref(v_wpConst_5760_);
                        leanh::lean_dec_ref(v_args_5759_);
                        leanh::lean_dec_ref(v_ent_5758_);
                        leanh::lean_dec_ref(v_00_u03c3s_5757_);
                        leanh::lean_dec_ref(v_H_5756_);
                        leanh::lean_dec_ref(v_head_5755_);
                        leanh::lean_dec(v_goal_5754_);
                        v_a_5814_ = leanh::lean_ctor_get(v___x_5779_, 0);
                        v_isSharedCheck_5821_ =
                            (!leanh::lean_is_exclusive(v___x_5779_)) as u8;
                        if v_isSharedCheck_5821_ == 0 {
                            v___x_5816_ = v___x_5779_;
                            v_isShared_5817_ = v_isSharedCheck_5821_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5814_);
                            leanh::lean_dec(v___x_5779_);
                            v___x_5816_ = leanh::lean_box(0);
                            v_isShared_5817_ = v_isSharedCheck_5821_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_5765_);
                    leanh::lean_dec_ref(v_00_u03b1_5764_);
                    leanh::lean_dec_ref(v_instWP_5763_);
                    leanh::lean_dec_ref(v_ps_5762_);
                    leanh::lean_dec_ref(v_m_5761_);
                    leanh::lean_dec_ref(v_wpConst_5760_);
                    leanh::lean_dec_ref(v_args_5759_);
                    leanh::lean_dec_ref(v_ent_5758_);
                    leanh::lean_dec_ref(v_00_u03c3s_5757_);
                    leanh::lean_dec_ref(v_H_5756_);
                    leanh::lean_dec_ref(v_head_5755_);
                    leanh::lean_dec(v_goal_5754_);
                    v___x_5822_ = leanh::lean_box(0);
                    v___x_5823_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5823_, 0, v___x_5822_);
                    return v___x_5823_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5780_) == 1 {
                    leanh::lean_del_object(v___x_5782_);
                    v_val_5784_ = leanh::lean_ctor_get(v_a_5780_, 0);
                    v_isSharedCheck_5808_ = (!leanh::lean_is_exclusive(v_a_5780_)) as u8;
                    if v_isSharedCheck_5808_ == 0 {
                        v___x_5786_ = v_a_5780_;
                        v_isShared_5787_ = v_isSharedCheck_5808_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5784_);
                        leanh::lean_dec(v_a_5780_);
                        v___x_5786_ = leanh::lean_box(0);
                        v_isShared_5787_ = v_isSharedCheck_5808_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5780_);
                    leanh::lean_dec_ref(v_00_u03b1_5764_);
                    leanh::lean_dec_ref(v_instWP_5763_);
                    leanh::lean_dec_ref(v_ps_5762_);
                    leanh::lean_dec_ref(v_m_5761_);
                    leanh::lean_dec_ref(v_wpConst_5760_);
                    leanh::lean_dec_ref(v_args_5759_);
                    leanh::lean_dec_ref(v_ent_5758_);
                    leanh::lean_dec_ref(v_00_u03c3s_5757_);
                    leanh::lean_dec_ref(v_H_5756_);
                    leanh::lean_dec_ref(v_head_5755_);
                    leanh::lean_dec(v_goal_5754_);
                    v___x_5809_ = leanh::lean_box(0);
                    if v_isShared_5783_ == 0 {
                        leanh::lean_ctor_set(v___x_5782_, 0, v___x_5809_);
                        v___x_5811_ = v___x_5782_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5812_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5812_, 0, v___x_5809_);
                        v___x_5811_ = v_reuseFailAlloc_5812_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5788_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_5754_, v_head_5755_, v_H_5756_, v_00_u03c3s_5757_, v_ent_5758_, v_args_5759_, v_wpConst_5760_, v_m_5761_, v_ps_5762_, v_instWP_5763_, v_00_u03b1_5764_, v_val_5784_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_);
                if leanh::lean_obj_tag(v___x_5788_) == 0 {
                    v_a_5789_ = leanh::lean_ctor_get(v___x_5788_, 0);
                    v_isSharedCheck_5799_ = (!leanh::lean_is_exclusive(v___x_5788_)) as u8;
                    if v_isSharedCheck_5799_ == 0 {
                        v___x_5791_ = v___x_5788_;
                        v_isShared_5792_ = v_isSharedCheck_5799_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5789_);
                        leanh::lean_dec(v___x_5788_);
                        v___x_5791_ = leanh::lean_box(0);
                        v_isShared_5792_ = v_isSharedCheck_5799_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5786_);
                    v_a_5800_ = leanh::lean_ctor_get(v___x_5788_, 0);
                    v_isSharedCheck_5807_ = (!leanh::lean_is_exclusive(v___x_5788_)) as u8;
                    if v_isSharedCheck_5807_ == 0 {
                        v___x_5802_ = v___x_5788_;
                        v_isShared_5803_ = v_isSharedCheck_5807_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5800_);
                        leanh::lean_dec(v___x_5788_);
                        v___x_5802_ = leanh::lean_box(0);
                        v_isShared_5803_ = v_isSharedCheck_5807_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5787_ == 0 {
                    leanh::lean_ctor_set(v___x_5786_, 0, v_a_5789_);
                    v___x_5794_ = v___x_5786_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5798_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_a_5789_);
                    v___x_5794_ = v_reuseFailAlloc_5798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5792_ == 0 {
                    leanh::lean_ctor_set(v___x_5791_, 0, v___x_5794_);
                    v___x_5796_ = v___x_5791_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5797_, 0, v___x_5794_);
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
                    v_reuseFailAlloc_5806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_a_5800_);
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
                    v_reuseFailAlloc_5820_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_a_5814_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_goal_5824_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_head_5825_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_H_5826_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_5827_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_ent_5828_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_args_5829_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_wpConst_5830_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_m_5831_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_ps_5832_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_instWP_5833_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_00_u03b1_5834_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_e_5835_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_f_5836_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_5837_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_5838_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_5839_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_5840_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_5841_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_5842_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_5843_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_a_5844_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_a_5845_: *mut leanh::LeanObject = *_args.add(21);
    let mut v_a_5846_: *mut leanh::LeanObject = *_args.add(22);
    let mut v_a_5847_: *mut leanh::LeanObject = *_args.add(23);
    let mut v_a_5848_: *mut leanh::LeanObject = *_args.add(24);
    let mut v_res_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5849_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceProg(v_goal_5824_, v_head_5825_, v_H_5826_, v_00_u03c3s_5827_, v_ent_5828_, v_args_5829_, v_wpConst_5830_, v_m_5831_, v_ps_5832_, v_instWP_5833_, v_00_u03b1_5834_, v_e_5835_, v_f_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_);
    leanh::lean_dec(v_a_5847_);
    leanh::lean_dec_ref(v_a_5846_);
    leanh::lean_dec(v_a_5845_);
    leanh::lean_dec_ref(v_a_5844_);
    leanh::lean_dec(v_a_5843_);
    leanh::lean_dec_ref(v_a_5842_);
    leanh::lean_dec(v_a_5841_);
    leanh::lean_dec_ref(v_a_5840_);
    leanh::lean_dec(v_a_5839_);
    leanh::lean_dec(v_a_5838_);
    leanh::lean_dec_ref(v_a_5837_);
    leanh::lean_dec_ref(v_f_5836_);
    return v_res_5849_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(
    mut v_cls_5850_: *mut leanh::LeanObject,
    mut v_____do__lift_5851_: *mut leanh::LeanObject,
    mut v___y_5852_: *mut leanh::LeanObject,
    mut v___y_5853_: *mut leanh::LeanObject,
    mut v___y_5854_: *mut leanh::LeanObject,
    mut v___y_5855_: *mut leanh::LeanObject,
    mut v___y_5856_: *mut leanh::LeanObject,
    mut v___y_5857_: *mut leanh::LeanObject,
    mut v___y_5858_: *mut leanh::LeanObject,
    mut v___y_5859_: *mut leanh::LeanObject,
    mut v___y_5860_: *mut leanh::LeanObject,
    mut v___y_5861_: *mut leanh::LeanObject,
    mut v___y_5862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5865_: u8 = 0;
    v_options_5864_ = leanh::lean_ctor_get(v___y_5861_, 2);
    v_hasTrace_5865_ = leanh::lean_ctor_get_uint8(
        v_options_5864_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_5865_ == 0 {
        let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_cls_5850_);
        v___x_5866_ = leanh::lean_box((v_hasTrace_5865_) as usize);
        v___x_5867_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5867_, 0, v___x_5866_);
        return v___x_5867_;
    } else {
        let mut v___x_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5870_: u8 = 0;
        let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5868_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8;
        v___x_5869_ = l_Lean_Name_append(v___x_5868_, v_cls_5850_);
        v___x_5870_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_5851_,
            v_options_5864_,
            v___x_5869_,
        );
        leanh::lean_dec(v___x_5869_);
        v___x_5871_ = leanh::lean_box((v___x_5870_) as usize);
        v___x_5872_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5872_, 0, v___x_5871_);
        return v___x_5872_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed(
    mut v_cls_5873_: *mut leanh::LeanObject,
    mut v_____do__lift_5874_: *mut leanh::LeanObject,
    mut v___y_5875_: *mut leanh::LeanObject,
    mut v___y_5876_: *mut leanh::LeanObject,
    mut v___y_5877_: *mut leanh::LeanObject,
    mut v___y_5878_: *mut leanh::LeanObject,
    mut v___y_5879_: *mut leanh::LeanObject,
    mut v___y_5880_: *mut leanh::LeanObject,
    mut v___y_5881_: *mut leanh::LeanObject,
    mut v___y_5882_: *mut leanh::LeanObject,
    mut v___y_5883_: *mut leanh::LeanObject,
    mut v___y_5884_: *mut leanh::LeanObject,
    mut v___y_5885_: *mut leanh::LeanObject,
    mut v___y_5886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5887_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(v_cls_5873_, v_____do__lift_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_);
    leanh::lean_dec(v___y_5885_);
    leanh::lean_dec_ref(v___y_5884_);
    leanh::lean_dec(v___y_5883_);
    leanh::lean_dec_ref(v___y_5882_);
    leanh::lean_dec(v___y_5881_);
    leanh::lean_dec_ref(v___y_5880_);
    leanh::lean_dec(v___y_5879_);
    leanh::lean_dec_ref(v___y_5878_);
    leanh::lean_dec(v___y_5877_);
    leanh::lean_dec(v___y_5876_);
    leanh::lean_dec_ref(v___y_5875_);
    leanh::lean_dec_ref(v_____do__lift_5874_);
    return v_res_5887_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(
    mut v_a_5888_: *mut leanh::LeanObject,
    mut v_a_5889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5895_: u8 = 0;
    let mut v___x_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5888_) == 0 {
                    v___x_5890_ = l_List_reverse___redArg(v_a_5889_);
                    return v___x_5890_;
                } else {
                    v_head_5891_ = leanh::lean_ctor_get(v_a_5888_, 0);
                    v_tail_5892_ = leanh::lean_ctor_get(v_a_5888_, 1);
                    v_isSharedCheck_5901_ = (!leanh::lean_is_exclusive(v_a_5888_)) as u8;
                    if v_isSharedCheck_5901_ == 0 {
                        v___x_5894_ = v_a_5888_;
                        v_isShared_5895_ = v_isSharedCheck_5901_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5892_);
                        leanh::lean_inc(v_head_5891_);
                        leanh::lean_dec(v_a_5888_);
                        v___x_5894_ = leanh::lean_box(0);
                        v_isShared_5895_ = v_isSharedCheck_5901_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5896_ = l_Lean_MessageData_ofExpr(v_head_5891_);
                if v_isShared_5895_ == 0 {
                    leanh::lean_ctor_set(v___x_5894_, 1, v_a_5889_);
                    leanh::lean_ctor_set(v___x_5894_, 0, v___x_5896_);
                    v___x_5898_ = v___x_5894_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5900_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5900_, 0, v___x_5896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5900_, 1, v_a_5889_);
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
-> *mut leanh::LeanObject {
    let mut v___x_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5903_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0;
    v___x_5904_ = l_Lean_stringToMessageData(v___x_5903_);
    return v___x_5904_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5906_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2;
    v___x_5907_ = l_Lean_stringToMessageData(v___x_5906_);
    return v___x_5907_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5909_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4;
    v___x_5910_ = l_Lean_stringToMessageData(v___x_5909_);
    return v___x_5910_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5912_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6;
    v___x_5913_ = l_Lean_stringToMessageData(v___x_5912_);
    return v___x_5913_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5915_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8;
    v___x_5916_ = l_Lean_stringToMessageData(v___x_5915_);
    return v___x_5916_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5918_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10;
    v___x_5919_ = l_Lean_stringToMessageData(v___x_5918_);
    return v___x_5919_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5921_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12;
    v___x_5922_ = l_Lean_stringToMessageData(v___x_5921_);
    return v___x_5922_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5924_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14;
    v___x_5925_ = l_Lean_stringToMessageData(v___x_5924_);
    return v___x_5925_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5927_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16;
    v___x_5928_ = l_Lean_stringToMessageData(v___x_5927_);
    return v___x_5928_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5930_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18;
    v___x_5931_ = l_Lean_stringToMessageData(v___x_5930_);
    return v___x_5931_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5933_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20;
    v___x_5934_ = l_Lean_stringToMessageData(v___x_5933_);
    return v___x_5934_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5938_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23;
    v___x_5939_ = l_Lean_stringToMessageData(v___x_5938_);
    return v___x_5939_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5941_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25;
    v___x_5942_ = l_Lean_stringToMessageData(v___x_5941_);
    return v___x_5942_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(
    mut v_scope_5943_: *mut leanh::LeanObject,
    mut v_goal_5944_: *mut leanh::LeanObject,
    mut v_e_5945_: *mut leanh::LeanObject,
    mut v_excessArgs_5946_: *mut leanh::LeanObject,
    mut v_m_5947_: *mut leanh::LeanObject,
    mut v_00_u03c3s_5948_: *mut leanh::LeanObject,
    mut v_ps_5949_: *mut leanh::LeanObject,
    mut v_instWP_5950_: *mut leanh::LeanObject,
    mut v_a_5951_: *mut leanh::LeanObject,
    mut v_a_5952_: *mut leanh::LeanObject,
    mut v_a_5953_: *mut leanh::LeanObject,
    mut v_a_5954_: *mut leanh::LeanObject,
    mut v_a_5955_: *mut leanh::LeanObject,
    mut v_a_5956_: *mut leanh::LeanObject,
    mut v_a_5957_: *mut leanh::LeanObject,
    mut v_a_5958_: *mut leanh::LeanObject,
    mut v_a_5959_: *mut leanh::LeanObject,
    mut v_a_5960_: *mut leanh::LeanObject,
    mut v_a_5961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5987_: u8 = 0;
    let mut v_mvarIds_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6004_: u8 = 0;
    let mut v___x_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6008_: u8 = 0;
    let mut v_isSharedCheck_6009_: u8 = 0;
    let mut v_a_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6013_: u8 = 0;
    let mut v___x_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6017_: u8 = 0;
    let mut v___y_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6042_: u8 = 0;
    let mut v_val_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: u8 = 0;
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6054_: u8 = 0;
    let mut v___x_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6058_: u8 = 0;
    let mut v___x_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: u8 = 0;
    let mut v_expr_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6075_: u8 = 0;
    let mut v___x_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6079_: u8 = 0;
    let mut v_a_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6083_: u8 = 0;
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6087_: u8 = 0;
    let mut v_a_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6091_: u8 = 0;
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6095_: u8 = 0;
    let mut v_a_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6099_: u8 = 0;
    let mut v___x_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6103_: u8 = 0;
    let mut v_a_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6107_: u8 = 0;
    let mut v___x_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6111_: u8 = 0;
    let mut v___y_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6134_: u8 = 0;
    let mut v___x_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut v___y_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_specs_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6158_: u8 = 0;
    let mut v___x_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6161_: u8 = 0;
    let mut v_a_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6169_: u8 = 0;
    let mut v_unused_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: u8 = 0;
    let mut v_proof_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6205_: u8 = 0;
    let mut v___x_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6209_: u8 = 0;
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v_a_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6214_: u8 = 0;
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6218_: u8 = 0;
    let mut v___y_6220_: u8 = 0;
    let mut v_inheritedTraceOptions_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: u8 = 0;
    let mut v___x_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6241_: u8 = 0;
    let mut v___x_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6245_: u8 = 0;
    let mut v_f_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_dec_ref(v_f_6246_);
                    v___y_6220_ = v___x_6248_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_f_6246_);
                    v___y_6220_ = v___x_6247_;
                    state = 35;
                    continue;
                }
            }
            1 => {
                v___x_5964_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5964_, 0, v_e_5945_);
                v___x_5965_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5965_, 0, v___x_5964_);
                return v___x_5965_;
            }
            2 => {
                v___x_5979_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
                v___x_5980_ = l_Lean_indentExpr(v_e_5945_);
                leanh::lean_inc_ref(v___x_5980_);
                v___x_5981_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5981_, 0, v___x_5979_);
                leanh::lean_ctor_set(v___x_5981_, 1, v___x_5980_);
                v___x_5982_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5982_, 0, v___x_5981_);
                leanh::lean_inc_ref(v___y_5967_);
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
                if leanh::lean_obj_tag(v___x_5983_) == 0 {
                    v_a_5984_ = leanh::lean_ctor_get(v___x_5983_, 0);
                    v_isSharedCheck_6009_ = (!leanh::lean_is_exclusive(v___x_5983_)) as u8;
                    if v_isSharedCheck_6009_ == 0 {
                        v___x_5986_ = v___x_5983_;
                        v_isShared_5987_ = v_isSharedCheck_6009_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5984_);
                        leanh::lean_dec(v___x_5983_);
                        v___x_5986_ = leanh::lean_box(0);
                        v_isShared_5987_ = v_isSharedCheck_6009_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5980_);
                    leanh::lean_dec_ref(v___y_5967_);
                    leanh::lean_dec_ref(v_scope_5943_);
                    v_a_6010_ = leanh::lean_ctor_get(v___x_5983_, 0);
                    v_isSharedCheck_6017_ = (!leanh::lean_is_exclusive(v___x_5983_)) as u8;
                    if v_isSharedCheck_6017_ == 0 {
                        v___x_6012_ = v___x_5983_;
                        v_isShared_6013_ = v_isSharedCheck_6017_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6010_);
                        leanh::lean_dec(v___x_5983_);
                        v___x_6012_ = leanh::lean_box(0);
                        v_isShared_6013_ = v_isSharedCheck_6017_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_5984_) == 1 {
                    leanh::lean_dec_ref(v___x_5980_);
                    leanh::lean_dec_ref(v___y_5967_);
                    v_mvarIds_5988_ = leanh::lean_ctor_get(v_a_5984_, 0);
                    leanh::lean_inc(v_mvarIds_5988_);
                    leanh::lean_dec_ref_known(v_a_5984_, 1);
                    v___x_5989_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5989_, 0, v_scope_5943_);
                    leanh::lean_ctor_set(v___x_5989_, 1, v_mvarIds_5988_);
                    if v_isShared_5987_ == 0 {
                        leanh::lean_ctor_set(v___x_5986_, 0, v___x_5989_);
                        v___x_5991_ = v___x_5986_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5992_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5992_, 0, v___x_5989_);
                        v___x_5991_ = v_reuseFailAlloc_5992_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5986_);
                    leanh::lean_dec(v_a_5984_);
                    leanh::lean_dec_ref(v_scope_5943_);
                    v_expr_5993_ = leanh::lean_ctor_get(v___y_5967_, 0);
                    leanh::lean_inc_ref(v_expr_5993_);
                    leanh::lean_dec_ref(v___y_5967_);
                    v___x_5994_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
                    v___x_5995_ = l_Lean_MessageData_ofExpr(v_expr_5993_);
                    v___x_5996_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5996_, 0, v___x_5994_);
                    leanh::lean_ctor_set(v___x_5996_, 1, v___x_5995_);
                    v___x_5997_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
                    v___x_5998_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5998_, 0, v___x_5996_);
                    leanh::lean_ctor_set(v___x_5998_, 1, v___x_5997_);
                    v___x_5999_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5999_, 0, v___x_5998_);
                    leanh::lean_ctor_set(v___x_5999_, 1, v___x_5980_);
                    v___x_6000_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_5999_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
                    v_a_6001_ = leanh::lean_ctor_get(v___x_6000_, 0);
                    v_isSharedCheck_6008_ = (!leanh::lean_is_exclusive(v___x_6000_)) as u8;
                    if v_isSharedCheck_6008_ == 0 {
                        v___x_6003_ = v___x_6000_;
                        v_isShared_6004_ = v_isSharedCheck_6008_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6001_);
                        leanh::lean_dec(v___x_6000_);
                        v___x_6003_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_6007_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6007_, 0, v_a_6001_);
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
                    v_reuseFailAlloc_6016_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_a_6010_);
                    v___x_6015_ = v_reuseFailAlloc_6016_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6015_;
            }
            9 => {
                v___x_6020_ = leanh::lean_box(0);
                v___x_6021_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6021_, 0, v___y_6019_);
                leanh::lean_ctor_set(v___x_6021_, 1, v___x_6020_);
                v___x_6022_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6022_, 0, v_scope_5943_);
                leanh::lean_ctor_set(v___x_6022_, 1, v___x_6021_);
                v___x_6023_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6023_, 0, v___x_6022_);
                return v___x_6023_;
            }
            10 => {
                leanh::lean_inc(v_goal_5944_);
                leanh::lean_inc_ref(v___y_6026_);
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
                if leanh::lean_obj_tag(v___x_6039_) == 0 {
                    v_a_6040_ = leanh::lean_ctor_get(v___x_6039_, 0);
                    leanh::lean_inc(v_a_6040_);
                    leanh::lean_dec_ref_known(v___x_6039_, 1);
                    if leanh::lean_obj_tag(v_a_6040_) == 1 {
                        leanh::lean_dec_ref(v___y_6026_);
                        leanh::lean_dec_ref(v_instWP_5950_);
                        leanh::lean_dec_ref(v_ps_5949_);
                        leanh::lean_dec_ref(v_00_u03c3s_5948_);
                        leanh::lean_dec_ref(v_m_5947_);
                        leanh::lean_dec_ref(v_excessArgs_5946_);
                        leanh::lean_dec_ref(v_e_5945_);
                        leanh::lean_dec(v_goal_5944_);
                        v_options_6041_ = leanh::lean_ctor_get(v___y_6037_, 2);
                        v_hasTrace_6042_ = leanh::lean_ctor_get_uint8(
                            v_options_6041_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_6042_ == 0 {
                            leanh::lean_dec(v___y_6027_);
                            v_val_6043_ = leanh::lean_ctor_get(v_a_6040_, 0);
                            leanh::lean_inc(v_val_6043_);
                            leanh::lean_dec_ref_known(v_a_6040_, 1);
                            v___y_6019_ = v_val_6043_;
                            state = 9;
                            continue;
                        } else {
                            v_val_6044_ = leanh::lean_ctor_get(v_a_6040_, 0);
                            leanh::lean_inc(v_val_6044_);
                            leanh::lean_dec_ref_known(v_a_6040_, 1);
                            v_inheritedTraceOptions_6045_ =
                                leanh::lean_ctor_get(v___y_6037_, 13);
                            v___x_6046_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8;
                            leanh::lean_inc(v___y_6027_);
                            v___x_6047_ = l_Lean_Name_append(v___x_6046_, v___y_6027_);
                            v___x_6048_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_6045_,
                                v_options_6041_,
                                v___x_6047_,
                            );
                            leanh::lean_dec(v___x_6047_);
                            if v___x_6048_ == 0 {
                                leanh::lean_dec(v___y_6027_);
                                v___y_6019_ = v_val_6044_;
                                state = 9;
                                continue;
                            } else {
                                v___x_6049_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
                                v___x_6050_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_6027_, v___x_6049_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_);
                                if leanh::lean_obj_tag(v___x_6050_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_6050_, 1);
                                    v___y_6019_ = v_val_6044_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_val_6044_);
                                    leanh::lean_dec_ref(v_scope_5943_);
                                    v_a_6051_ = leanh::lean_ctor_get(v___x_6050_, 0);
                                    v_isSharedCheck_6058_ =
                                        (!leanh::lean_is_exclusive(v___x_6050_)) as u8;
                                    if v_isSharedCheck_6058_ == 0 {
                                        v___x_6053_ = v___x_6050_;
                                        v_isShared_6054_ = v_isSharedCheck_6058_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6051_);
                                        leanh::lean_dec(v___x_6050_);
                                        v___x_6053_ = leanh::lean_box(0);
                                        v_isShared_6054_ = v_isSharedCheck_6058_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_6040_);
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
                        if leanh::lean_obj_tag(v___x_6059_) == 0 {
                            v_a_6060_ = leanh::lean_ctor_get(v___x_6059_, 0);
                            leanh::lean_inc(v_a_6060_);
                            leanh::lean_dec_ref_known(v___x_6059_, 1);
                            v_inheritedTraceOptions_6061_ =
                                leanh::lean_ctor_get(v___y_6037_, 13);
                            leanh::lean_inc_ref(v___y_6025_);
                            leanh::lean_inc(v___y_6038_);
                            leanh::lean_inc_ref(v___y_6037_);
                            leanh::lean_inc(v___y_6036_);
                            leanh::lean_inc_ref(v___y_6035_);
                            leanh::lean_inc(v___y_6034_);
                            leanh::lean_inc_ref(v___y_6033_);
                            leanh::lean_inc(v___y_6032_);
                            leanh::lean_inc_ref(v___y_6031_);
                            leanh::lean_inc(v___y_6030_);
                            leanh::lean_inc(v___y_6029_);
                            leanh::lean_inc_ref(v___y_6028_);
                            leanh::lean_inc_ref(v_inheritedTraceOptions_6061_);
                            v___x_6062_ = leanh::lean_apply_13(
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
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_6062_) == 0 {
                                v_a_6063_ = leanh::lean_ctor_get(v___x_6062_, 0);
                                leanh::lean_inc(v_a_6063_);
                                leanh::lean_dec_ref_known(v___x_6062_, 1);
                                v___x_6064_ = (leanh::lean_unbox(v_a_6063_) as u8);
                                leanh::lean_dec(v_a_6063_);
                                if v___x_6064_ == 0 {
                                    leanh::lean_dec(v___y_6027_);
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
                                    v_expr_6065_ = leanh::lean_ctor_get(v_a_6060_, 0);
                                    leanh::lean_inc(v___y_6038_);
                                    leanh::lean_inc_ref(v___y_6037_);
                                    leanh::lean_inc(v___y_6036_);
                                    leanh::lean_inc_ref(v___y_6035_);
                                    leanh::lean_inc_ref(v_expr_6065_);
                                    v___x_6066_ = lean_infer_type(
                                        v_expr_6065_,
                                        v___y_6035_,
                                        v___y_6036_,
                                        v___y_6037_,
                                        v___y_6038_,
                                    );
                                    if leanh::lean_obj_tag(v___x_6066_) == 0 {
                                        v_a_6067_ = leanh::lean_ctor_get(v___x_6066_, 0);
                                        leanh::lean_inc(v_a_6067_);
                                        leanh::lean_dec_ref_known(v___x_6066_, 1);
                                        v___x_6068_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9);
                                        v___x_6069_ = l_Lean_MessageData_ofExpr(v_a_6067_);
                                        v___x_6070_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_6070_, 0, v___x_6068_);
                                        leanh::lean_ctor_set(v___x_6070_, 1, v___x_6069_);
                                        v___x_6071_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_6027_, v___x_6070_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_);
                                        if leanh::lean_obj_tag(v___x_6071_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_6071_, 1);
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
                                            leanh::lean_dec(v_a_6060_);
                                            leanh::lean_dec_ref(v_e_5945_);
                                            leanh::lean_dec(v_goal_5944_);
                                            leanh::lean_dec_ref(v_scope_5943_);
                                            v_a_6072_ = leanh::lean_ctor_get(v___x_6071_, 0);
                                            v_isSharedCheck_6079_ =
                                                (!leanh::lean_is_exclusive(v___x_6071_))
                                                    as u8;
                                            if v_isSharedCheck_6079_ == 0 {
                                                v___x_6074_ = v___x_6071_;
                                                v_isShared_6075_ = v_isSharedCheck_6079_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_6072_);
                                                leanh::lean_dec(v___x_6071_);
                                                v___x_6074_ = leanh::lean_box(0);
                                                v_isShared_6075_ = v_isSharedCheck_6079_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_6060_);
                                        leanh::lean_dec(v___y_6027_);
                                        leanh::lean_dec_ref(v_e_5945_);
                                        leanh::lean_dec(v_goal_5944_);
                                        leanh::lean_dec_ref(v_scope_5943_);
                                        v_a_6080_ = leanh::lean_ctor_get(v___x_6066_, 0);
                                        v_isSharedCheck_6087_ =
                                            (!leanh::lean_is_exclusive(v___x_6066_)) as u8;
                                        if v_isSharedCheck_6087_ == 0 {
                                            v___x_6082_ = v___x_6066_;
                                            v_isShared_6083_ = v_isSharedCheck_6087_;
                                            state = 15;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6080_);
                                            leanh::lean_dec(v___x_6066_);
                                            v___x_6082_ = leanh::lean_box(0);
                                            v_isShared_6083_ = v_isSharedCheck_6087_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_6060_);
                                leanh::lean_dec(v___y_6027_);
                                leanh::lean_dec_ref(v_e_5945_);
                                leanh::lean_dec(v_goal_5944_);
                                leanh::lean_dec_ref(v_scope_5943_);
                                v_a_6088_ = leanh::lean_ctor_get(v___x_6062_, 0);
                                v_isSharedCheck_6095_ =
                                    (!leanh::lean_is_exclusive(v___x_6062_)) as u8;
                                if v_isSharedCheck_6095_ == 0 {
                                    v___x_6090_ = v___x_6062_;
                                    v_isShared_6091_ = v_isSharedCheck_6095_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6088_);
                                    leanh::lean_dec(v___x_6062_);
                                    v___x_6090_ = leanh::lean_box(0);
                                    v_isShared_6091_ = v_isSharedCheck_6095_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___y_6027_);
                            leanh::lean_dec_ref(v_e_5945_);
                            leanh::lean_dec(v_goal_5944_);
                            leanh::lean_dec_ref(v_scope_5943_);
                            v_a_6096_ = leanh::lean_ctor_get(v___x_6059_, 0);
                            v_isSharedCheck_6103_ =
                                (!leanh::lean_is_exclusive(v___x_6059_)) as u8;
                            if v_isSharedCheck_6103_ == 0 {
                                v___x_6098_ = v___x_6059_;
                                v_isShared_6099_ = v_isSharedCheck_6103_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6096_);
                                leanh::lean_dec(v___x_6059_);
                                v___x_6098_ = leanh::lean_box(0);
                                v_isShared_6099_ = v_isSharedCheck_6103_;
                                state = 19;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_6027_);
                    leanh::lean_dec_ref(v___y_6026_);
                    leanh::lean_dec_ref(v_instWP_5950_);
                    leanh::lean_dec_ref(v_ps_5949_);
                    leanh::lean_dec_ref(v_00_u03c3s_5948_);
                    leanh::lean_dec_ref(v_m_5947_);
                    leanh::lean_dec_ref(v_excessArgs_5946_);
                    leanh::lean_dec_ref(v_e_5945_);
                    leanh::lean_dec(v_goal_5944_);
                    leanh::lean_dec_ref(v_scope_5943_);
                    v_a_6104_ = leanh::lean_ctor_get(v___x_6039_, 0);
                    v_isSharedCheck_6111_ = (!leanh::lean_is_exclusive(v___x_6039_)) as u8;
                    if v_isSharedCheck_6111_ == 0 {
                        v___x_6106_ = v___x_6039_;
                        v_isShared_6107_ = v_isSharedCheck_6111_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6104_);
                        leanh::lean_dec(v___x_6039_);
                        v___x_6106_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_6057_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6057_, 0, v_a_6051_);
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
                    v_reuseFailAlloc_6078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6078_, 0, v_a_6072_);
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
                    v_reuseFailAlloc_6086_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6086_, 0, v_a_6080_);
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
                    v_reuseFailAlloc_6094_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6094_, 0, v_a_6088_);
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
                    v_reuseFailAlloc_6102_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6102_, 0, v_a_6096_);
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
                    v_reuseFailAlloc_6110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
                    v___x_6109_ = v_reuseFailAlloc_6110_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6109_;
            }
            23 => {
                v___x_6129_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6129_, 0, v___y_6115_);
                leanh::lean_ctor_set(v___x_6129_, 1, v___y_6128_);
                leanh::lean_inc(v___y_6125_);
                v___x_6130_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_6125_, v___x_6129_, v___y_6123_, v___y_6118_, v___y_6124_, v___y_6117_);
                if leanh::lean_obj_tag(v___x_6130_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6130_, 1);
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
                    leanh::lean_dec(v___y_6125_);
                    leanh::lean_dec_ref(v___y_6122_);
                    leanh::lean_dec_ref(v_instWP_5950_);
                    leanh::lean_dec_ref(v_ps_5949_);
                    leanh::lean_dec_ref(v_00_u03c3s_5948_);
                    leanh::lean_dec_ref(v_m_5947_);
                    leanh::lean_dec_ref(v_excessArgs_5946_);
                    leanh::lean_dec_ref(v_e_5945_);
                    leanh::lean_dec(v_goal_5944_);
                    leanh::lean_dec_ref(v_scope_5943_);
                    v_a_6131_ = leanh::lean_ctor_get(v___x_6130_, 0);
                    v_isSharedCheck_6138_ = (!leanh::lean_is_exclusive(v___x_6130_)) as u8;
                    if v_isSharedCheck_6138_ == 0 {
                        v___x_6133_ = v___x_6130_;
                        v_isShared_6134_ = v_isSharedCheck_6138_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6131_);
                        leanh::lean_dec(v___x_6130_);
                        v___x_6133_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_6137_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6137_, 0, v_a_6131_);
                    v___x_6136_ = v_reuseFailAlloc_6137_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6136_;
            }
            26 => {
                v_specs_6153_ = leanh::lean_ctor_get(v_scope_5943_, 0);
                leanh::lean_inc_ref(v_e_5945_);
                leanh::lean_inc_ref(v_specs_6153_);
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
                if leanh::lean_obj_tag(v___x_6154_) == 0 {
                    v_a_6155_ = leanh::lean_ctor_get(v___x_6154_, 0);
                    v_isSharedCheck_6210_ = (!leanh::lean_is_exclusive(v___x_6154_)) as u8;
                    if v_isSharedCheck_6210_ == 0 {
                        v___x_6157_ = v___x_6154_;
                        v_isShared_6158_ = v_isSharedCheck_6210_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6155_);
                        leanh::lean_dec(v___x_6154_);
                        v___x_6157_ = leanh::lean_box(0);
                        v_isShared_6158_ = v_isSharedCheck_6210_;
                        state = 27;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_6141_);
                    leanh::lean_dec_ref(v_instWP_5950_);
                    leanh::lean_dec_ref(v_ps_5949_);
                    leanh::lean_dec_ref(v_00_u03c3s_5948_);
                    leanh::lean_dec_ref(v_m_5947_);
                    leanh::lean_dec_ref(v_excessArgs_5946_);
                    leanh::lean_dec_ref(v_e_5945_);
                    leanh::lean_dec(v_goal_5944_);
                    leanh::lean_dec_ref(v_scope_5943_);
                    v_a_6211_ = leanh::lean_ctor_get(v___x_6154_, 0);
                    v_isSharedCheck_6218_ = (!leanh::lean_is_exclusive(v___x_6154_)) as u8;
                    if v_isSharedCheck_6218_ == 0 {
                        v___x_6213_ = v___x_6154_;
                        v_isShared_6214_ = v_isSharedCheck_6218_;
                        state = 33;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6211_);
                        leanh::lean_dec(v___x_6154_);
                        v___x_6213_ = leanh::lean_box(0);
                        v_isShared_6214_ = v_isSharedCheck_6218_;
                        state = 33;
                        continue;
                    }
                }
            }
            27 => {
                if leanh::lean_obj_tag(v_a_6155_) == 0 {
                    leanh::lean_dec(v___y_6141_);
                    leanh::lean_dec_ref(v_instWP_5950_);
                    leanh::lean_dec_ref(v_ps_5949_);
                    leanh::lean_dec_ref(v_00_u03c3s_5948_);
                    leanh::lean_dec_ref(v_excessArgs_5946_);
                    leanh::lean_dec(v_goal_5944_);
                    v_isSharedCheck_6169_ = (!leanh::lean_is_exclusive(v_scope_5943_)) as u8;
                    if v_isSharedCheck_6169_ == 0 {
                        v_unused_6170_ = leanh::lean_ctor_get(v_scope_5943_, 2);
                        leanh::lean_dec(v_unused_6170_);
                        v_unused_6171_ = leanh::lean_ctor_get(v_scope_5943_, 1);
                        leanh::lean_dec(v_unused_6171_);
                        v_unused_6172_ = leanh::lean_ctor_get(v_scope_5943_, 0);
                        leanh::lean_dec(v_unused_6172_);
                        v___x_6160_ = v_scope_5943_;
                        v_isShared_6161_ = v_isSharedCheck_6169_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_dec(v_scope_5943_);
                        v___x_6160_ = leanh::lean_box(0);
                        v_isShared_6161_ = v_isSharedCheck_6169_;
                        state = 28;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6157_);
                    v_a_6173_ = leanh::lean_ctor_get(v_a_6155_, 0);
                    leanh::lean_inc(v_a_6173_);
                    leanh::lean_dec_ref_known(v_a_6155_, 1);
                    v_inheritedTraceOptions_6174_ = leanh::lean_ctor_get(v___y_6151_, 13);
                    leanh::lean_inc_ref(v___y_6140_);
                    leanh::lean_inc(v___y_6152_);
                    leanh::lean_inc_ref(v___y_6151_);
                    leanh::lean_inc(v___y_6150_);
                    leanh::lean_inc_ref(v___y_6149_);
                    leanh::lean_inc(v___y_6148_);
                    leanh::lean_inc_ref(v___y_6147_);
                    leanh::lean_inc(v___y_6146_);
                    leanh::lean_inc_ref(v___y_6145_);
                    leanh::lean_inc(v___y_6144_);
                    leanh::lean_inc(v___y_6143_);
                    leanh::lean_inc_ref(v___y_6142_);
                    leanh::lean_inc_ref(v_inheritedTraceOptions_6174_);
                    v___x_6175_ = leanh::lean_apply_13(
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
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_6175_) == 0 {
                        v_a_6176_ = leanh::lean_ctor_get(v___x_6175_, 0);
                        leanh::lean_inc(v_a_6176_);
                        leanh::lean_dec_ref_known(v___x_6175_, 1);
                        v___x_6177_ = (leanh::lean_unbox(v_a_6176_) as u8);
                        leanh::lean_dec(v_a_6176_);
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
                            v_proof_6178_ = leanh::lean_ctor_get(v_a_6173_, 1);
                            v___x_6179_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11);
                            leanh::lean_inc_ref(v_e_5945_);
                            v___x_6180_ = l_Lean_MessageData_ofExpr(v_e_5945_);
                            v___x_6181_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6181_, 0, v___x_6179_);
                            leanh::lean_ctor_set(v___x_6181_, 1, v___x_6180_);
                            v___x_6182_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13);
                            v___x_6183_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6183_, 0, v___x_6181_);
                            leanh::lean_ctor_set(v___x_6183_, 1, v___x_6182_);
                            match leanh::lean_obj_tag(v_proof_6178_) {
                                0 => {
                                    v_declName_6184_ =
                                        leanh::lean_ctor_get(v_proof_6178_, 0);
                                    v___x_6185_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15);
                                    leanh::lean_inc(v_declName_6184_);
                                    v___x_6186_ = l_Lean_MessageData_ofName(v_declName_6184_);
                                    v___x_6187_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6187_, 0, v___x_6185_);
                                    leanh::lean_ctor_set(v___x_6187_, 1, v___x_6186_);
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
                                    v_fvarId_6188_ = leanh::lean_ctor_get(v_proof_6178_, 0);
                                    v___x_6189_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17);
                                    leanh::lean_inc(v_fvarId_6188_);
                                    v___x_6190_ = l_Lean_mkFVar(v_fvarId_6188_);
                                    v___x_6191_ = l_Lean_MessageData_ofExpr(v___x_6190_);
                                    v___x_6192_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6192_, 0, v___x_6189_);
                                    leanh::lean_ctor_set(v___x_6192_, 1, v___x_6191_);
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
                                    v_ref_6193_ = leanh::lean_ctor_get(v_proof_6178_, 1);
                                    v_proof_6194_ = leanh::lean_ctor_get(v_proof_6178_, 2);
                                    v___x_6195_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19);
                                    leanh::lean_inc(v_ref_6193_);
                                    v___x_6196_ = l_Lean_MessageData_ofSyntax(v_ref_6193_);
                                    v___x_6197_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6197_, 0, v___x_6195_);
                                    leanh::lean_ctor_set(v___x_6197_, 1, v___x_6196_);
                                    v___x_6198_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21);
                                    v___x_6199_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6199_, 0, v___x_6197_);
                                    leanh::lean_ctor_set(v___x_6199_, 1, v___x_6198_);
                                    leanh::lean_inc_ref(v_proof_6194_);
                                    v___x_6200_ = l_Lean_MessageData_ofExpr(v_proof_6194_);
                                    v___x_6201_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6201_, 0, v___x_6199_);
                                    leanh::lean_ctor_set(v___x_6201_, 1, v___x_6200_);
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
                        leanh::lean_dec(v_a_6173_);
                        leanh::lean_dec(v___y_6141_);
                        leanh::lean_dec_ref(v_instWP_5950_);
                        leanh::lean_dec_ref(v_ps_5949_);
                        leanh::lean_dec_ref(v_00_u03c3s_5948_);
                        leanh::lean_dec_ref(v_m_5947_);
                        leanh::lean_dec_ref(v_excessArgs_5946_);
                        leanh::lean_dec_ref(v_e_5945_);
                        leanh::lean_dec(v_goal_5944_);
                        leanh::lean_dec_ref(v_scope_5943_);
                        v_a_6202_ = leanh::lean_ctor_get(v___x_6175_, 0);
                        v_isSharedCheck_6209_ =
                            (!leanh::lean_is_exclusive(v___x_6175_)) as u8;
                        if v_isSharedCheck_6209_ == 0 {
                            v___x_6204_ = v___x_6175_;
                            v_isShared_6205_ = v_isSharedCheck_6209_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6202_);
                            leanh::lean_dec(v___x_6175_);
                            v___x_6204_ = leanh::lean_box(0);
                            v_isShared_6205_ = v_isSharedCheck_6209_;
                            state = 31;
                            continue;
                        }
                    }
                }
            }
            28 => {
                v_a_6162_ = leanh::lean_ctor_get(v_a_6155_, 0);
                leanh::lean_inc(v_a_6162_);
                leanh::lean_dec_ref_known(v_a_6155_, 1);
                if v_isShared_6161_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6160_, 3);
                    leanh::lean_ctor_set(v___x_6160_, 2, v_a_6162_);
                    leanh::lean_ctor_set(v___x_6160_, 1, v_m_5947_);
                    leanh::lean_ctor_set(v___x_6160_, 0, v_e_5945_);
                    v___x_6164_ = v___x_6160_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6168_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6168_, 0, v_e_5945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6168_, 1, v_m_5947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6168_, 2, v_a_6162_);
                    v___x_6164_ = v_reuseFailAlloc_6168_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_6158_ == 0 {
                    leanh::lean_ctor_set(v___x_6157_, 0, v___x_6164_);
                    v___x_6166_ = v___x_6157_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6167_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6167_, 0, v___x_6164_);
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
                    v_reuseFailAlloc_6208_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6208_, 0, v_a_6202_);
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
                    v_reuseFailAlloc_6217_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6217_, 0, v_a_6211_);
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
                    leanh::lean_dec_ref(v_instWP_5950_);
                    leanh::lean_dec_ref(v_ps_5949_);
                    leanh::lean_dec_ref(v_00_u03c3s_5948_);
                    leanh::lean_dec_ref(v_m_5947_);
                    leanh::lean_dec_ref(v_excessArgs_5946_);
                    leanh::lean_dec(v_goal_5944_);
                    leanh::lean_dec_ref(v_scope_5943_);
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_6221_ = leanh::lean_ctor_get(v_a_5960_, 13);
                    v_cls_6222_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6;
                    v___f_6223_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22;
                    v___x_6224_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(v_cls_6222_, v_inheritedTraceOptions_6221_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_, v_a_5961_);
                    v_a_6225_ = leanh::lean_ctor_get(v___x_6224_, 0);
                    leanh::lean_inc(v_a_6225_);
                    leanh::lean_dec_ref(v___x_6224_);
                    v___x_6226_ = (leanh::lean_unbox(v_a_6225_) as u8);
                    leanh::lean_dec(v_a_6225_);
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
                        v___x_6227_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24);
                        leanh::lean_inc_ref(v_e_5945_);
                        v___x_6228_ = l_Lean_MessageData_ofExpr(v_e_5945_);
                        v___x_6229_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6229_, 0, v___x_6227_);
                        leanh::lean_ctor_set(v___x_6229_, 1, v___x_6228_);
                        v___x_6230_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26);
                        v___x_6231_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6231_, 0, v___x_6229_);
                        leanh::lean_ctor_set(v___x_6231_, 1, v___x_6230_);
                        leanh::lean_inc_ref(v_excessArgs_5946_);
                        v___x_6232_ = lean_array_to_list(v_excessArgs_5946_);
                        v___x_6233_ = leanh::lean_box(0);
                        v___x_6234_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_6232_, v___x_6233_);
                        v___x_6235_ = l_Lean_MessageData_ofList(v___x_6234_);
                        v___x_6236_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6236_, 0, v___x_6231_);
                        leanh::lean_ctor_set(v___x_6236_, 1, v___x_6235_);
                        v___x_6237_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_6222_, v___x_6236_, v_a_5958_, v_a_5959_, v_a_5960_, v_a_5961_);
                        if leanh::lean_obj_tag(v___x_6237_) == 0 {
                            leanh::lean_dec_ref_known(v___x_6237_, 1);
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
                            leanh::lean_dec_ref(v_instWP_5950_);
                            leanh::lean_dec_ref(v_ps_5949_);
                            leanh::lean_dec_ref(v_00_u03c3s_5948_);
                            leanh::lean_dec_ref(v_m_5947_);
                            leanh::lean_dec_ref(v_excessArgs_5946_);
                            leanh::lean_dec_ref(v_e_5945_);
                            leanh::lean_dec(v_goal_5944_);
                            leanh::lean_dec_ref(v_scope_5943_);
                            v_a_6238_ = leanh::lean_ctor_get(v___x_6237_, 0);
                            v_isSharedCheck_6245_ =
                                (!leanh::lean_is_exclusive(v___x_6237_)) as u8;
                            if v_isSharedCheck_6245_ == 0 {
                                v___x_6240_ = v___x_6237_;
                                v_isShared_6241_ = v_isSharedCheck_6245_;
                                state = 36;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6238_);
                                leanh::lean_dec(v___x_6237_);
                                v___x_6240_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_6244_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6244_, 0, v_a_6238_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_scope_6249_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_goal_6250_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_e_6251_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_excessArgs_6252_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_m_6253_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_00_u03c3s_6254_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_ps_6255_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_instWP_6256_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_6257_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_6258_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_6259_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_6260_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_6261_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_6262_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_6263_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_6264_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_6265_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_6266_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_6267_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_6268_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_res_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6269_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_scope_6249_, v_goal_6250_, v_e_6251_, v_excessArgs_6252_, v_m_6253_, v_00_u03c3s_6254_, v_ps_6255_, v_instWP_6256_, v_a_6257_, v_a_6258_, v_a_6259_, v_a_6260_, v_a_6261_, v_a_6262_, v_a_6263_, v_a_6264_, v_a_6265_, v_a_6266_, v_a_6267_);
    leanh::lean_dec(v_a_6267_);
    leanh::lean_dec_ref(v_a_6266_);
    leanh::lean_dec(v_a_6265_);
    leanh::lean_dec_ref(v_a_6264_);
    leanh::lean_dec(v_a_6263_);
    leanh::lean_dec_ref(v_a_6262_);
    leanh::lean_dec(v_a_6261_);
    leanh::lean_dec_ref(v_a_6260_);
    leanh::lean_dec(v_a_6259_);
    leanh::lean_dec(v_a_6258_);
    leanh::lean_dec_ref(v_a_6257_);
    return v_res_6269_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0(
    mut v_x_6270_: *mut leanh::LeanObject,
    mut v___y_6271_: *mut leanh::LeanObject,
    mut v___y_6272_: *mut leanh::LeanObject,
    mut v___y_6273_: *mut leanh::LeanObject,
    mut v___y_6274_: *mut leanh::LeanObject,
    mut v___y_6275_: *mut leanh::LeanObject,
    mut v___y_6276_: *mut leanh::LeanObject,
    mut v___y_6277_: *mut leanh::LeanObject,
    mut v___y_6278_: *mut leanh::LeanObject,
    mut v___y_6279_: *mut leanh::LeanObject,
    mut v___y_6280_: *mut leanh::LeanObject,
    mut v___y_6281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_6277_);
    leanh::lean_inc_ref(v___y_6276_);
    leanh::lean_inc(v___y_6275_);
    leanh::lean_inc_ref(v___y_6274_);
    leanh::lean_inc(v___y_6273_);
    leanh::lean_inc(v___y_6272_);
    leanh::lean_inc_ref(v___y_6271_);
    v___x_6283_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_6283_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0___boxed(
    mut v_x_6284_: *mut leanh::LeanObject,
    mut v___y_6285_: *mut leanh::LeanObject,
    mut v___y_6286_: *mut leanh::LeanObject,
    mut v___y_6287_: *mut leanh::LeanObject,
    mut v___y_6288_: *mut leanh::LeanObject,
    mut v___y_6289_: *mut leanh::LeanObject,
    mut v___y_6290_: *mut leanh::LeanObject,
    mut v___y_6291_: *mut leanh::LeanObject,
    mut v___y_6292_: *mut leanh::LeanObject,
    mut v___y_6293_: *mut leanh::LeanObject,
    mut v___y_6294_: *mut leanh::LeanObject,
    mut v___y_6295_: *mut leanh::LeanObject,
    mut v___y_6296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6297_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0(v_x_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_, v___y_6294_, v___y_6295_);
    leanh::lean_dec(v___y_6291_);
    leanh::lean_dec_ref(v___y_6290_);
    leanh::lean_dec(v___y_6289_);
    leanh::lean_dec_ref(v___y_6288_);
    leanh::lean_dec(v___y_6287_);
    leanh::lean_dec(v___y_6286_);
    leanh::lean_dec_ref(v___y_6285_);
    return v_res_6297_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(
    mut v_mvarId_6298_: *mut leanh::LeanObject,
    mut v_x_6299_: *mut leanh::LeanObject,
    mut v___y_6300_: *mut leanh::LeanObject,
    mut v___y_6301_: *mut leanh::LeanObject,
    mut v___y_6302_: *mut leanh::LeanObject,
    mut v___y_6303_: *mut leanh::LeanObject,
    mut v___y_6304_: *mut leanh::LeanObject,
    mut v___y_6305_: *mut leanh::LeanObject,
    mut v___y_6306_: *mut leanh::LeanObject,
    mut v___y_6307_: *mut leanh::LeanObject,
    mut v___y_6308_: *mut leanh::LeanObject,
    mut v___y_6309_: *mut leanh::LeanObject,
    mut v___y_6310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6317_: u8 = 0;
    let mut v___x_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_6306_);
                leanh::lean_inc_ref(v___y_6305_);
                leanh::lean_inc(v___y_6304_);
                leanh::lean_inc_ref(v___y_6303_);
                leanh::lean_inc(v___y_6302_);
                leanh::lean_inc(v___y_6301_);
                leanh::lean_inc_ref(v___y_6300_);
                v___f_6312_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                leanh::lean_closure_set(v___f_6312_, 0, v_x_6299_);
                leanh::lean_closure_set(v___f_6312_, 1, v___y_6300_);
                leanh::lean_closure_set(v___f_6312_, 2, v___y_6301_);
                leanh::lean_closure_set(v___f_6312_, 3, v___y_6302_);
                leanh::lean_closure_set(v___f_6312_, 4, v___y_6303_);
                leanh::lean_closure_set(v___f_6312_, 5, v___y_6304_);
                leanh::lean_closure_set(v___f_6312_, 6, v___y_6305_);
                leanh::lean_closure_set(v___f_6312_, 7, v___y_6306_);
                v___x_6313_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_6298_,
                    v___f_6312_,
                    v___y_6307_,
                    v___y_6308_,
                    v___y_6309_,
                    v___y_6310_,
                );
                if leanh::lean_obj_tag(v___x_6313_) == 0 {
                    return v___x_6313_;
                } else {
                    v_a_6314_ = leanh::lean_ctor_get(v___x_6313_, 0);
                    v_isSharedCheck_6321_ = (!leanh::lean_is_exclusive(v___x_6313_)) as u8;
                    if v_isSharedCheck_6321_ == 0 {
                        v___x_6316_ = v___x_6313_;
                        v_isShared_6317_ = v_isSharedCheck_6321_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6314_);
                        leanh::lean_dec(v___x_6313_);
                        v___x_6316_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_6320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6320_, 0, v_a_6314_);
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
    mut v_mvarId_6322_: *mut leanh::LeanObject,
    mut v_x_6323_: *mut leanh::LeanObject,
    mut v___y_6324_: *mut leanh::LeanObject,
    mut v___y_6325_: *mut leanh::LeanObject,
    mut v___y_6326_: *mut leanh::LeanObject,
    mut v___y_6327_: *mut leanh::LeanObject,
    mut v___y_6328_: *mut leanh::LeanObject,
    mut v___y_6329_: *mut leanh::LeanObject,
    mut v___y_6330_: *mut leanh::LeanObject,
    mut v___y_6331_: *mut leanh::LeanObject,
    mut v___y_6332_: *mut leanh::LeanObject,
    mut v___y_6333_: *mut leanh::LeanObject,
    mut v___y_6334_: *mut leanh::LeanObject,
    mut v___y_6335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6336_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_mvarId_6322_, v_x_6323_, v___y_6324_, v___y_6325_, v___y_6326_, v___y_6327_, v___y_6328_, v___y_6329_, v___y_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
    leanh::lean_dec(v___y_6334_);
    leanh::lean_dec_ref(v___y_6333_);
    leanh::lean_dec(v___y_6332_);
    leanh::lean_dec_ref(v___y_6331_);
    leanh::lean_dec(v___y_6330_);
    leanh::lean_dec_ref(v___y_6329_);
    leanh::lean_dec(v___y_6328_);
    leanh::lean_dec_ref(v___y_6327_);
    leanh::lean_dec(v___y_6326_);
    leanh::lean_dec(v___y_6325_);
    leanh::lean_dec_ref(v___y_6324_);
    return v_res_6336_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1(
    mut v_00_u03b1_6337_: *mut leanh::LeanObject,
    mut v_mvarId_6338_: *mut leanh::LeanObject,
    mut v_x_6339_: *mut leanh::LeanObject,
    mut v___y_6340_: *mut leanh::LeanObject,
    mut v___y_6341_: *mut leanh::LeanObject,
    mut v___y_6342_: *mut leanh::LeanObject,
    mut v___y_6343_: *mut leanh::LeanObject,
    mut v___y_6344_: *mut leanh::LeanObject,
    mut v___y_6345_: *mut leanh::LeanObject,
    mut v___y_6346_: *mut leanh::LeanObject,
    mut v___y_6347_: *mut leanh::LeanObject,
    mut v___y_6348_: *mut leanh::LeanObject,
    mut v___y_6349_: *mut leanh::LeanObject,
    mut v___y_6350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6352_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_mvarId_6338_, v_x_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_, v___y_6349_, v___y_6350_);
    return v___x_6352_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___boxed(
    mut v_00_u03b1_6353_: *mut leanh::LeanObject,
    mut v_mvarId_6354_: *mut leanh::LeanObject,
    mut v_x_6355_: *mut leanh::LeanObject,
    mut v___y_6356_: *mut leanh::LeanObject,
    mut v___y_6357_: *mut leanh::LeanObject,
    mut v___y_6358_: *mut leanh::LeanObject,
    mut v___y_6359_: *mut leanh::LeanObject,
    mut v___y_6360_: *mut leanh::LeanObject,
    mut v___y_6361_: *mut leanh::LeanObject,
    mut v___y_6362_: *mut leanh::LeanObject,
    mut v___y_6363_: *mut leanh::LeanObject,
    mut v___y_6364_: *mut leanh::LeanObject,
    mut v___y_6365_: *mut leanh::LeanObject,
    mut v___y_6366_: *mut leanh::LeanObject,
    mut v___y_6367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_6366_);
    leanh::lean_dec_ref(v___y_6365_);
    leanh::lean_dec(v___y_6364_);
    leanh::lean_dec_ref(v___y_6363_);
    leanh::lean_dec(v___y_6362_);
    leanh::lean_dec_ref(v___y_6361_);
    leanh::lean_dec(v___y_6360_);
    leanh::lean_dec_ref(v___y_6359_);
    leanh::lean_dec(v___y_6358_);
    leanh::lean_dec(v___y_6357_);
    leanh::lean_dec_ref(v___y_6356_);
    return v_res_6368_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__0(
    mut v_x_6369_: *mut leanh::LeanObject,
    mut v_x_6370_: *mut leanh::LeanObject,
    mut v_x_6371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6369_) == 5 {
                    v_fn_6372_ = leanh::lean_ctor_get(v_x_6369_, 0);
                    leanh::lean_inc_ref(v_fn_6372_);
                    v_arg_6373_ = leanh::lean_ctor_get(v_x_6369_, 1);
                    leanh::lean_inc_ref(v_arg_6373_);
                    leanh::lean_dec_ref_known(v_x_6369_, 2);
                    v___x_6374_ = lean_array_set(v_x_6370_, v_x_6371_, v_arg_6373_);
                    v___x_6375_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6376_ = lean_nat_sub(v_x_6371_, v___x_6375_);
                    leanh::lean_dec(v_x_6371_);
                    v_x_6369_ = v_fn_6372_;
                    v_x_6370_ = v___x_6374_;
                    v_x_6371_ = v___x_6376_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_6371_);
                    v___x_6378_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6378_, 0, v_x_6369_);
                    leanh::lean_ctor_set(v___x_6378_, 1, v_x_6370_);
                    return v___x_6378_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6384_ = leanh::lean_box(0);
    v_dummy_6385_ = l_Lean_Expr_sort___override(v___x_6384_);
    return v_dummy_6385_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6401_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8;
    v___x_6402_ = l_Lean_stringToMessageData(v___x_6401_);
    return v___x_6402_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6404_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10;
    v___x_6405_ = l_Lean_stringToMessageData(v___x_6404_);
    return v___x_6405_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(
    mut v_goal_6406_: *mut leanh::LeanObject,
    mut v_scope_6407_: *mut leanh::LeanObject,
    mut v___y_6408_: *mut leanh::LeanObject,
    mut v___y_6409_: *mut leanh::LeanObject,
    mut v___y_6410_: *mut leanh::LeanObject,
    mut v___y_6411_: *mut leanh::LeanObject,
    mut v___y_6412_: *mut leanh::LeanObject,
    mut v___y_6413_: *mut leanh::LeanObject,
    mut v___y_6414_: *mut leanh::LeanObject,
    mut v___y_6415_: *mut leanh::LeanObject,
    mut v___y_6416_: *mut leanh::LeanObject,
    mut v___y_6417_: *mut leanh::LeanObject,
    mut v___y_6418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gs_6421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_6425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_6436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6441_: u8 = 0;
    let mut v___x_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6448_: u8 = 0;
    let mut v_unused_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6453_: u8 = 0;
    let mut v___x_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6457_: u8 = 0;
    let mut v___y_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6489_: u8 = 0;
    let mut v___x_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6496_: u8 = 0;
    let mut v_unused_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6501_: u8 = 0;
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut v___x_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6514_: u8 = 0;
    let mut v___x_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6519_: u8 = 0;
    let mut v_unused_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6524_: u8 = 0;
    let mut v___x_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v___x_6529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6540_: u8 = 0;
    let mut v___x_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6544_: u8 = 0;
    let mut v_a_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6548_: u8 = 0;
    let mut v___x_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6552_: u8 = 0;
    let mut v_a_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6556_: u8 = 0;
    let mut v___x_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6560_: u8 = 0;
    let mut v_a_6561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6564_: u8 = 0;
    let mut v___x_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6568_: u8 = 0;
    let mut v_a_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6572_: u8 = 0;
    let mut v___x_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6576_: u8 = 0;
    let mut v_a_6577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6580_: u8 = 0;
    let mut v___x_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6584_: u8 = 0;
    let mut v___x_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6589_: u8 = 0;
    let mut v___x_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6597_: u8 = 0;
    let mut v_cls_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6624_: u8 = 0;
    let mut v_arg_6625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: u8 = 0;
    let mut v_arg_6628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: u8 = 0;
    let mut v_arg_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: u8 = 0;
    let mut v___x_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v___x_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: u8 = 0;
    let mut v___x_6654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6658_: u8 = 0;
    let mut v_val_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6664_: u8 = 0;
    let mut v_a_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6668_: u8 = 0;
    let mut v___x_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6672_: u8 = 0;
    let mut v___x_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: u8 = 0;
    let mut v_arg_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: u8 = 0;
    let mut v_arg_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: u8 = 0;
    let mut v_arg_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: u8 = 0;
    let mut v_arg_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: u8 = 0;
    let mut v_arg_6690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: u8 = 0;
    let mut v_options_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6696_: u8 = 0;
    let mut v___x_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: u8 = 0;
    let mut v___x_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6711_: u8 = 0;
    let mut v___x_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6715_: u8 = 0;
    let mut v_reuseFailAlloc_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6717_: u8 = 0;
    let mut v_a_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6721_: u8 = 0;
    let mut v___x_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6725_: u8 = 0;
    let mut v_a_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6729_: u8 = 0;
    let mut v___x_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6733_: u8 = 0;
    let mut v_a_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6737_: u8 = 0;
    let mut v___x_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6741_: u8 = 0;
    let mut v_a_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6745_: u8 = 0;
    let mut v___x_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6749_: u8 = 0;
    let mut v_a_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6753_: u8 = 0;
    let mut v___x_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6757_: u8 = 0;
    let mut v_a_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6761_: u8 = 0;
    let mut v___x_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6765_: u8 = 0;
    let mut v___x_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: u8 = 0;
    let mut v___x_6768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6775_: u8 = 0;
    let mut v___x_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6779_: u8 = 0;
    let mut v_isSharedCheck_6780_: u8 = 0;
    let mut v_a_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6784_: u8 = 0;
    let mut v___x_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_goal_6406_);
                v___x_6585_ = l_Lean_MVarId_getType(
                    v_goal_6406_,
                    v___y_6415_,
                    v___y_6416_,
                    v___y_6417_,
                    v___y_6418_,
                );
                if leanh::lean_obj_tag(v___x_6585_) == 0 {
                    v_a_6586_ = leanh::lean_ctor_get(v___x_6585_, 0);
                    v_isSharedCheck_6780_ = (!leanh::lean_is_exclusive(v___x_6585_)) as u8;
                    if v_isSharedCheck_6780_ == 0 {
                        v___x_6588_ = v___x_6585_;
                        v_isShared_6589_ = v_isSharedCheck_6780_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6586_);
                        leanh::lean_dec(v___x_6585_);
                        v___x_6588_ = leanh::lean_box(0);
                        v_isShared_6589_ = v_isSharedCheck_6780_;
                        state = 30;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_scope_6407_);
                    leanh::lean_dec(v_goal_6406_);
                    v_a_6781_ = leanh::lean_ctor_get(v___x_6585_, 0);
                    v_isSharedCheck_6788_ = (!leanh::lean_is_exclusive(v___x_6585_)) as u8;
                    if v_isSharedCheck_6788_ == 0 {
                        v___x_6783_ = v___x_6585_;
                        v_isShared_6784_ = v_isSharedCheck_6788_;
                        state = 56;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6781_);
                        leanh::lean_dec(v___x_6585_);
                        v___x_6783_ = leanh::lean_box(0);
                        v_isShared_6784_ = v_isSharedCheck_6788_;
                        state = 56;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6422_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6422_, 0, v_scope_6407_);
                leanh::lean_ctor_set(v___x_6422_, 1, v_gs_6421_);
                v___x_6423_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6423_, 0, v___x_6422_);
                return v___x_6423_;
            }
            2 => {
                v___x_6426_ = leanh::lean_box(0);
                v___x_6427_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6427_, 0, v_g_6425_);
                leanh::lean_ctor_set(v___x_6427_, 1, v___x_6426_);
                v___x_6428_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6428_, 0, v_scope_6407_);
                leanh::lean_ctor_set(v___x_6428_, 1, v___x_6427_);
                v___x_6429_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6429_, 0, v___x_6428_);
                return v___x_6429_;
            }
            3 => {
                v___x_6432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6432_, 0, v___y_6431_);
                v___x_6433_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6433_, 0, v___x_6432_);
                return v___x_6433_;
            }
            4 => {
                v___x_6438_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_6437_);
                if leanh::lean_obj_tag(v___x_6438_) == 0 {
                    v_isSharedCheck_6448_ = (!leanh::lean_is_exclusive(v___x_6438_)) as u8;
                    if v_isSharedCheck_6448_ == 0 {
                        v_unused_6449_ = leanh::lean_ctor_get(v___x_6438_, 0);
                        leanh::lean_dec(v_unused_6449_);
                        v___x_6440_ = v___x_6438_;
                        v_isShared_6441_ = v_isSharedCheck_6448_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6438_);
                        v___x_6440_ = leanh::lean_box(0);
                        v_isShared_6441_ = v_isSharedCheck_6448_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_g_6436_);
                    leanh::lean_dec_ref(v___y_6435_);
                    v_a_6450_ = leanh::lean_ctor_get(v___x_6438_, 0);
                    v_isSharedCheck_6457_ = (!leanh::lean_is_exclusive(v___x_6438_)) as u8;
                    if v_isSharedCheck_6457_ == 0 {
                        v___x_6452_ = v___x_6438_;
                        v_isShared_6453_ = v_isSharedCheck_6457_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6450_);
                        leanh::lean_dec(v___x_6438_);
                        v___x_6452_ = leanh::lean_box(0);
                        v_isShared_6453_ = v_isSharedCheck_6457_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_6442_ = leanh::lean_box(0);
                v___x_6443_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6443_, 0, v_g_6436_);
                leanh::lean_ctor_set(v___x_6443_, 1, v___x_6442_);
                v___x_6444_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6444_, 0, v___y_6435_);
                leanh::lean_ctor_set(v___x_6444_, 1, v___x_6443_);
                if v_isShared_6441_ == 0 {
                    leanh::lean_ctor_set(v___x_6440_, 0, v___x_6444_);
                    v___x_6446_ = v___x_6440_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6447_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6447_, 0, v___x_6444_);
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
                    v_reuseFailAlloc_6456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_a_6450_);
                    v___x_6455_ = v_reuseFailAlloc_6456_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6455_;
            }
            9 => {
                leanh::lean_inc_ref(v___y_6461_);
                leanh::lean_inc_ref(v___y_6459_);
                leanh::lean_inc_ref(v___y_6470_);
                leanh::lean_inc_ref(v___y_6464_);
                leanh::lean_inc_ref(v___y_6462_);
                leanh::lean_inc_ref(v___y_6465_);
                leanh::lean_inc_ref(v___y_6467_);
                leanh::lean_inc_ref(v___y_6463_);
                leanh::lean_inc_ref(v___y_6466_);
                leanh::lean_inc_ref(v___y_6460_);
                leanh::lean_inc_ref(v___y_6469_);
                leanh::lean_inc_ref(v___y_6468_);
                leanh::lean_inc(v_goal_6406_);
                v___x_6483_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(v_goal_6406_, v___y_6468_, v___y_6469_, v___y_6460_, v___y_6466_, v___y_6463_, v___y_6467_, v___y_6465_, v___y_6462_, v___y_6464_, v___y_6470_, v___y_6459_, v___y_6461_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                if leanh::lean_obj_tag(v___x_6483_) == 0 {
                    v_a_6484_ = leanh::lean_ctor_get(v___x_6483_, 0);
                    leanh::lean_inc(v_a_6484_);
                    leanh::lean_dec_ref_known(v___x_6483_, 1);
                    if leanh::lean_obj_tag(v_a_6484_) == 1 {
                        leanh::lean_dec_ref(v___y_6471_);
                        leanh::lean_dec_ref(v___y_6470_);
                        leanh::lean_dec_ref(v___y_6469_);
                        leanh::lean_dec_ref(v___y_6468_);
                        leanh::lean_dec_ref(v___y_6467_);
                        leanh::lean_dec_ref(v___y_6466_);
                        leanh::lean_dec_ref(v___y_6465_);
                        leanh::lean_dec_ref(v___y_6464_);
                        leanh::lean_dec_ref(v___y_6463_);
                        leanh::lean_dec_ref(v___y_6462_);
                        leanh::lean_dec_ref(v___y_6461_);
                        leanh::lean_dec_ref(v___y_6460_);
                        leanh::lean_dec_ref(v___y_6459_);
                        leanh::lean_dec(v_goal_6406_);
                        v_val_6485_ = leanh::lean_ctor_get(v_a_6484_, 0);
                        leanh::lean_inc(v_val_6485_);
                        leanh::lean_dec_ref_known(v_a_6484_, 1);
                        v___x_6486_ =
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_6473_);
                        if leanh::lean_obj_tag(v___x_6486_) == 0 {
                            v_isSharedCheck_6496_ =
                                (!leanh::lean_is_exclusive(v___x_6486_)) as u8;
                            if v_isSharedCheck_6496_ == 0 {
                                v_unused_6497_ = leanh::lean_ctor_get(v___x_6486_, 0);
                                leanh::lean_dec(v_unused_6497_);
                                v___x_6488_ = v___x_6486_;
                                v_isShared_6489_ = v_isSharedCheck_6496_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_6486_);
                                v___x_6488_ = leanh::lean_box(0);
                                v_isShared_6489_ = v_isSharedCheck_6496_;
                                state = 10;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_6485_);
                            leanh::lean_dec_ref(v_scope_6407_);
                            v_a_6498_ = leanh::lean_ctor_get(v___x_6486_, 0);
                            v_isSharedCheck_6505_ =
                                (!leanh::lean_is_exclusive(v___x_6486_)) as u8;
                            if v_isSharedCheck_6505_ == 0 {
                                v___x_6500_ = v___x_6486_;
                                v_isShared_6501_ = v_isSharedCheck_6505_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6498_);
                                leanh::lean_dec(v___x_6486_);
                                v___x_6500_ = leanh::lean_box(0);
                                v_isShared_6501_ = v_isSharedCheck_6505_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_6484_);
                        leanh::lean_inc(v_goal_6406_);
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
                        if leanh::lean_obj_tag(v___x_6506_) == 0 {
                            v_a_6507_ = leanh::lean_ctor_get(v___x_6506_, 0);
                            leanh::lean_inc(v_a_6507_);
                            leanh::lean_dec_ref_known(v___x_6506_, 1);
                            leanh::lean_inc_ref(v___y_6471_);
                            leanh::lean_inc_ref(v___y_6459_);
                            leanh::lean_inc_ref(v___y_6470_);
                            leanh::lean_inc_ref(v___y_6464_);
                            leanh::lean_inc_ref(v___y_6462_);
                            leanh::lean_inc_ref(v___y_6465_);
                            leanh::lean_inc_ref(v___y_6467_);
                            leanh::lean_inc_ref(v___y_6463_);
                            leanh::lean_inc_ref(v___y_6466_);
                            leanh::lean_inc_ref(v___y_6460_);
                            leanh::lean_inc_ref(v___y_6469_);
                            leanh::lean_inc_ref(v___y_6468_);
                            leanh::lean_inc(v_goal_6406_);
                            v___x_6508_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(v_goal_6406_, v___y_6468_, v___y_6469_, v___y_6460_, v___y_6466_, v___y_6463_, v___y_6467_, v___y_6465_, v___y_6462_, v___y_6464_, v___y_6470_, v___y_6459_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                            if leanh::lean_obj_tag(v___x_6508_) == 0 {
                                v_a_6509_ = leanh::lean_ctor_get(v___x_6508_, 0);
                                leanh::lean_inc(v_a_6509_);
                                leanh::lean_dec_ref_known(v___x_6508_, 1);
                                if leanh::lean_obj_tag(v_a_6509_) == 1 {
                                    leanh::lean_dec_ref(v___y_6471_);
                                    leanh::lean_dec_ref(v___y_6470_);
                                    leanh::lean_dec_ref(v___y_6469_);
                                    leanh::lean_dec_ref(v___y_6468_);
                                    leanh::lean_dec_ref(v___y_6467_);
                                    leanh::lean_dec_ref(v___y_6466_);
                                    leanh::lean_dec_ref(v___y_6465_);
                                    leanh::lean_dec_ref(v___y_6464_);
                                    leanh::lean_dec_ref(v___y_6463_);
                                    leanh::lean_dec_ref(v___y_6462_);
                                    leanh::lean_dec_ref(v___y_6461_);
                                    leanh::lean_dec_ref(v___y_6460_);
                                    leanh::lean_dec_ref(v___y_6459_);
                                    leanh::lean_dec(v_goal_6406_);
                                    v_val_6510_ = leanh::lean_ctor_get(v_a_6509_, 0);
                                    leanh::lean_inc(v_val_6510_);
                                    leanh::lean_dec_ref_known(v_a_6509_, 1);
                                    v___x_6511_ =
                                        l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(
                                            v___y_6473_,
                                        );
                                    if leanh::lean_obj_tag(v___x_6511_) == 0 {
                                        v_isSharedCheck_6519_ =
                                            (!leanh::lean_is_exclusive(v___x_6511_)) as u8;
                                        if v_isSharedCheck_6519_ == 0 {
                                            v_unused_6520_ =
                                                leanh::lean_ctor_get(v___x_6511_, 0);
                                            leanh::lean_dec(v_unused_6520_);
                                            v___x_6513_ = v___x_6511_;
                                            v_isShared_6514_ = v_isSharedCheck_6519_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_6511_);
                                            v___x_6513_ = leanh::lean_box(0);
                                            v_isShared_6514_ = v_isSharedCheck_6519_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_val_6510_);
                                        leanh::lean_dec(v_a_6507_);
                                        v_a_6521_ = leanh::lean_ctor_get(v___x_6511_, 0);
                                        v_isSharedCheck_6528_ =
                                            (!leanh::lean_is_exclusive(v___x_6511_)) as u8;
                                        if v_isSharedCheck_6528_ == 0 {
                                            v___x_6523_ = v___x_6511_;
                                            v_isShared_6524_ = v_isSharedCheck_6528_;
                                            state = 16;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6521_);
                                            leanh::lean_dec(v___x_6511_);
                                            v___x_6523_ = leanh::lean_box(0);
                                            v_isShared_6524_ = v_isSharedCheck_6528_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_6509_);
                                    leanh::lean_inc_ref(v___y_6459_);
                                    leanh::lean_inc_ref(v___y_6470_);
                                    leanh::lean_inc_ref(v___y_6464_);
                                    leanh::lean_inc_ref(v___y_6462_);
                                    leanh::lean_inc_ref(v___y_6465_);
                                    leanh::lean_inc_ref(v___y_6467_);
                                    leanh::lean_inc_ref(v___y_6463_);
                                    leanh::lean_inc_ref(v___y_6466_);
                                    leanh::lean_inc_ref(v___y_6460_);
                                    leanh::lean_inc_ref(v___y_6469_);
                                    leanh::lean_inc_ref(v___y_6468_);
                                    leanh::lean_inc(v_goal_6406_);
                                    v___x_6529_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(v_goal_6406_, v___y_6468_, v___y_6469_, v___y_6460_, v___y_6466_, v___y_6463_, v___y_6467_, v___y_6465_, v___y_6462_, v___y_6464_, v___y_6470_, v___y_6459_, v___y_6461_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                                    if leanh::lean_obj_tag(v___x_6529_) == 0 {
                                        v_a_6530_ = leanh::lean_ctor_get(v___x_6529_, 0);
                                        leanh::lean_inc(v_a_6530_);
                                        leanh::lean_dec_ref_known(v___x_6529_, 1);
                                        if leanh::lean_obj_tag(v_a_6530_) == 1 {
                                            leanh::lean_dec_ref(v___y_6471_);
                                            leanh::lean_dec_ref(v___y_6470_);
                                            leanh::lean_dec_ref(v___y_6469_);
                                            leanh::lean_dec_ref(v___y_6468_);
                                            leanh::lean_dec_ref(v___y_6467_);
                                            leanh::lean_dec_ref(v___y_6466_);
                                            leanh::lean_dec_ref(v___y_6465_);
                                            leanh::lean_dec_ref(v___y_6464_);
                                            leanh::lean_dec_ref(v___y_6463_);
                                            leanh::lean_dec_ref(v___y_6462_);
                                            leanh::lean_dec_ref(v___y_6461_);
                                            leanh::lean_dec_ref(v___y_6460_);
                                            leanh::lean_dec_ref(v___y_6459_);
                                            leanh::lean_dec(v_goal_6406_);
                                            v_val_6531_ = leanh::lean_ctor_get(v_a_6530_, 0);
                                            leanh::lean_inc(v_val_6531_);
                                            leanh::lean_dec_ref_known(v_a_6530_, 1);
                                            v___y_6435_ = v_a_6507_;
                                            v_g_6436_ = v_val_6531_;
                                            v___y_6437_ = v___y_6473_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v_a_6530_);
                                            leanh::lean_inc_ref(v___y_6459_);
                                            leanh::lean_inc_ref(v___y_6464_);
                                            leanh::lean_inc_ref(v___y_6462_);
                                            leanh::lean_inc_ref(v___y_6465_);
                                            leanh::lean_inc_ref(v___y_6460_);
                                            leanh::lean_inc(v_goal_6406_);
                                            v___x_6532_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceProg(v_goal_6406_, v___y_6468_, v___y_6469_, v___y_6460_, v___y_6466_, v___y_6463_, v___y_6467_, v___y_6465_, v___y_6462_, v___y_6464_, v___y_6470_, v___y_6459_, v___y_6461_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                                            leanh::lean_dec_ref(v___y_6461_);
                                            if leanh::lean_obj_tag(v___x_6532_) == 0 {
                                                v_a_6533_ =
                                                    leanh::lean_ctor_get(v___x_6532_, 0);
                                                leanh::lean_inc(v_a_6533_);
                                                leanh::lean_dec_ref_known(v___x_6532_, 1);
                                                if leanh::lean_obj_tag(v_a_6533_) == 1 {
                                                    leanh::lean_dec_ref(v___y_6471_);
                                                    leanh::lean_dec_ref(v___y_6465_);
                                                    leanh::lean_dec_ref(v___y_6464_);
                                                    leanh::lean_dec_ref(v___y_6462_);
                                                    leanh::lean_dec_ref(v___y_6460_);
                                                    leanh::lean_dec_ref(v___y_6459_);
                                                    leanh::lean_dec(v_goal_6406_);
                                                    v_val_6534_ =
                                                        leanh::lean_ctor_get(v_a_6533_, 0);
                                                    leanh::lean_inc(v_val_6534_);
                                                    leanh::lean_dec_ref_known(v_a_6533_, 1);
                                                    v___y_6435_ = v_a_6507_;
                                                    v_g_6436_ = v_val_6534_;
                                                    v___y_6437_ = v___y_6473_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    leanh::lean_dec(v_a_6533_);
                                                    v___x_6535_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_6473_);
                                                    if leanh::lean_obj_tag(v___x_6535_) == 0
                                                    {
                                                        leanh::lean_dec_ref_known(
                                                            v___x_6535_,
                                                            1,
                                                        );
                                                        v___x_6536_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_a_6507_, v_goal_6406_, v___y_6459_, v___y_6471_, v___y_6465_, v___y_6460_, v___y_6462_, v___y_6464_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                                                        return v___x_6536_;
                                                    } else {
                                                        leanh::lean_dec(v_a_6507_);
                                                        leanh::lean_dec_ref(v___y_6471_);
                                                        leanh::lean_dec_ref(v___y_6465_);
                                                        leanh::lean_dec_ref(v___y_6464_);
                                                        leanh::lean_dec_ref(v___y_6462_);
                                                        leanh::lean_dec_ref(v___y_6460_);
                                                        leanh::lean_dec_ref(v___y_6459_);
                                                        leanh::lean_dec(v_goal_6406_);
                                                        v_a_6537_ = leanh::lean_ctor_get(
                                                            v___x_6535_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_6544_ =
                                                            (!leanh::lean_is_exclusive(
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
                                                            leanh::lean_inc(v_a_6537_);
                                                            leanh::lean_dec(v___x_6535_);
                                                            v___x_6539_ = leanh::lean_box(0);
                                                            v_isShared_6540_ =
                                                                v_isSharedCheck_6544_;
                                                            state = 18;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec(v_a_6507_);
                                                leanh::lean_dec_ref(v___y_6471_);
                                                leanh::lean_dec_ref(v___y_6465_);
                                                leanh::lean_dec_ref(v___y_6464_);
                                                leanh::lean_dec_ref(v___y_6462_);
                                                leanh::lean_dec_ref(v___y_6460_);
                                                leanh::lean_dec_ref(v___y_6459_);
                                                leanh::lean_dec(v_goal_6406_);
                                                v_a_6545_ =
                                                    leanh::lean_ctor_get(v___x_6532_, 0);
                                                v_isSharedCheck_6552_ =
                                                    (!leanh::lean_is_exclusive(v___x_6532_))
                                                        as u8;
                                                if v_isSharedCheck_6552_ == 0 {
                                                    v___x_6547_ = v___x_6532_;
                                                    v_isShared_6548_ = v_isSharedCheck_6552_;
                                                    state = 20;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_6545_);
                                                    leanh::lean_dec(v___x_6532_);
                                                    v___x_6547_ = leanh::lean_box(0);
                                                    v_isShared_6548_ = v_isSharedCheck_6552_;
                                                    state = 20;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_6507_);
                                        leanh::lean_dec_ref(v___y_6471_);
                                        leanh::lean_dec_ref(v___y_6470_);
                                        leanh::lean_dec_ref(v___y_6469_);
                                        leanh::lean_dec_ref(v___y_6468_);
                                        leanh::lean_dec_ref(v___y_6467_);
                                        leanh::lean_dec_ref(v___y_6466_);
                                        leanh::lean_dec_ref(v___y_6465_);
                                        leanh::lean_dec_ref(v___y_6464_);
                                        leanh::lean_dec_ref(v___y_6463_);
                                        leanh::lean_dec_ref(v___y_6462_);
                                        leanh::lean_dec_ref(v___y_6461_);
                                        leanh::lean_dec_ref(v___y_6460_);
                                        leanh::lean_dec_ref(v___y_6459_);
                                        leanh::lean_dec(v_goal_6406_);
                                        v_a_6553_ = leanh::lean_ctor_get(v___x_6529_, 0);
                                        v_isSharedCheck_6560_ =
                                            (!leanh::lean_is_exclusive(v___x_6529_)) as u8;
                                        if v_isSharedCheck_6560_ == 0 {
                                            v___x_6555_ = v___x_6529_;
                                            v_isShared_6556_ = v_isSharedCheck_6560_;
                                            state = 22;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6553_);
                                            leanh::lean_dec(v___x_6529_);
                                            v___x_6555_ = leanh::lean_box(0);
                                            v_isShared_6556_ = v_isSharedCheck_6560_;
                                            state = 22;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_6507_);
                                leanh::lean_dec_ref(v___y_6471_);
                                leanh::lean_dec_ref(v___y_6470_);
                                leanh::lean_dec_ref(v___y_6469_);
                                leanh::lean_dec_ref(v___y_6468_);
                                leanh::lean_dec_ref(v___y_6467_);
                                leanh::lean_dec_ref(v___y_6466_);
                                leanh::lean_dec_ref(v___y_6465_);
                                leanh::lean_dec_ref(v___y_6464_);
                                leanh::lean_dec_ref(v___y_6463_);
                                leanh::lean_dec_ref(v___y_6462_);
                                leanh::lean_dec_ref(v___y_6461_);
                                leanh::lean_dec_ref(v___y_6460_);
                                leanh::lean_dec_ref(v___y_6459_);
                                leanh::lean_dec(v_goal_6406_);
                                v_a_6561_ = leanh::lean_ctor_get(v___x_6508_, 0);
                                v_isSharedCheck_6568_ =
                                    (!leanh::lean_is_exclusive(v___x_6508_)) as u8;
                                if v_isSharedCheck_6568_ == 0 {
                                    v___x_6563_ = v___x_6508_;
                                    v_isShared_6564_ = v_isSharedCheck_6568_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6561_);
                                    leanh::lean_dec(v___x_6508_);
                                    v___x_6563_ = leanh::lean_box(0);
                                    v_isShared_6564_ = v_isSharedCheck_6568_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___y_6471_);
                            leanh::lean_dec_ref(v___y_6470_);
                            leanh::lean_dec_ref(v___y_6469_);
                            leanh::lean_dec_ref(v___y_6468_);
                            leanh::lean_dec_ref(v___y_6467_);
                            leanh::lean_dec_ref(v___y_6466_);
                            leanh::lean_dec_ref(v___y_6465_);
                            leanh::lean_dec_ref(v___y_6464_);
                            leanh::lean_dec_ref(v___y_6463_);
                            leanh::lean_dec_ref(v___y_6462_);
                            leanh::lean_dec_ref(v___y_6461_);
                            leanh::lean_dec_ref(v___y_6460_);
                            leanh::lean_dec_ref(v___y_6459_);
                            leanh::lean_dec(v_goal_6406_);
                            v_a_6569_ = leanh::lean_ctor_get(v___x_6506_, 0);
                            v_isSharedCheck_6576_ =
                                (!leanh::lean_is_exclusive(v___x_6506_)) as u8;
                            if v_isSharedCheck_6576_ == 0 {
                                v___x_6571_ = v___x_6506_;
                                v_isShared_6572_ = v_isSharedCheck_6576_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6569_);
                                leanh::lean_dec(v___x_6506_);
                                v___x_6571_ = leanh::lean_box(0);
                                v_isShared_6572_ = v_isSharedCheck_6576_;
                                state = 26;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6471_);
                    leanh::lean_dec_ref(v___y_6470_);
                    leanh::lean_dec_ref(v___y_6469_);
                    leanh::lean_dec_ref(v___y_6468_);
                    leanh::lean_dec_ref(v___y_6467_);
                    leanh::lean_dec_ref(v___y_6466_);
                    leanh::lean_dec_ref(v___y_6465_);
                    leanh::lean_dec_ref(v___y_6464_);
                    leanh::lean_dec_ref(v___y_6463_);
                    leanh::lean_dec_ref(v___y_6462_);
                    leanh::lean_dec_ref(v___y_6461_);
                    leanh::lean_dec_ref(v___y_6460_);
                    leanh::lean_dec_ref(v___y_6459_);
                    leanh::lean_dec_ref(v_scope_6407_);
                    leanh::lean_dec(v_goal_6406_);
                    v_a_6577_ = leanh::lean_ctor_get(v___x_6483_, 0);
                    v_isSharedCheck_6584_ = (!leanh::lean_is_exclusive(v___x_6483_)) as u8;
                    if v_isSharedCheck_6584_ == 0 {
                        v___x_6579_ = v___x_6483_;
                        v_isShared_6580_ = v_isSharedCheck_6584_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6577_);
                        leanh::lean_dec(v___x_6483_);
                        v___x_6579_ = leanh::lean_box(0);
                        v_isShared_6580_ = v_isSharedCheck_6584_;
                        state = 28;
                        continue;
                    }
                }
            }
            10 => {
                v___x_6490_ = leanh::lean_box(0);
                v___x_6491_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6491_, 0, v_val_6485_);
                leanh::lean_ctor_set(v___x_6491_, 1, v___x_6490_);
                v___x_6492_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6492_, 0, v_scope_6407_);
                leanh::lean_ctor_set(v___x_6492_, 1, v___x_6491_);
                if v_isShared_6489_ == 0 {
                    leanh::lean_ctor_set(v___x_6488_, 0, v___x_6492_);
                    v___x_6494_ = v___x_6488_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6495_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6495_, 0, v___x_6492_);
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
                    v_reuseFailAlloc_6504_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6498_);
                    v___x_6503_ = v_reuseFailAlloc_6504_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6503_;
            }
            14 => {
                v___x_6515_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6515_, 0, v_a_6507_);
                leanh::lean_ctor_set(v___x_6515_, 1, v_val_6510_);
                if v_isShared_6514_ == 0 {
                    leanh::lean_ctor_set(v___x_6513_, 0, v___x_6515_);
                    v___x_6517_ = v___x_6513_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6518_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6518_, 0, v___x_6515_);
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
                    v_reuseFailAlloc_6527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6521_);
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
                    v_reuseFailAlloc_6543_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_a_6537_);
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
                    v_reuseFailAlloc_6551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6551_, 0, v_a_6545_);
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
                    v_reuseFailAlloc_6559_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_a_6553_);
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
                    v_reuseFailAlloc_6567_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6567_, 0, v_a_6561_);
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
                    v_reuseFailAlloc_6575_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_a_6569_);
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
                    v_reuseFailAlloc_6583_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6583_, 0, v_a_6577_);
                    v___x_6582_ = v_reuseFailAlloc_6583_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6582_;
            }
            30 => {
                v_options_6595_ = leanh::lean_ctor_get(v___y_6417_, 2);
                v_inheritedTraceOptions_6596_ = leanh::lean_ctor_get(v___y_6417_, 13);
                v_hasTrace_6597_ = leanh::lean_ctor_get_uint8(
                    v_options_6595_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                    v___x_6766_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
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
                        v___x_6768_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11);
                        leanh::lean_inc(v_a_6586_);
                        v___x_6769_ = l_Lean_MessageData_ofExpr(v_a_6586_);
                        v___x_6770_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6770_, 0, v___x_6768_);
                        leanh::lean_ctor_set(v___x_6770_, 1, v___x_6769_);
                        v___x_6771_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_6598_, v___x_6770_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_);
                        if leanh::lean_obj_tag(v___x_6771_) == 0 {
                            leanh::lean_dec_ref_known(v___x_6771_, 1);
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
                            leanh::lean_del_object(v___x_6588_);
                            leanh::lean_dec(v_a_6586_);
                            leanh::lean_dec_ref(v_scope_6407_);
                            leanh::lean_dec(v_goal_6406_);
                            v_a_6772_ = leanh::lean_ctor_get(v___x_6771_, 0);
                            v_isSharedCheck_6779_ =
                                (!leanh::lean_is_exclusive(v___x_6771_)) as u8;
                            if v_isSharedCheck_6779_ == 0 {
                                v___x_6774_ = v___x_6771_;
                                v_isShared_6775_ = v_isSharedCheck_6779_;
                                state = 54;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6772_);
                                leanh::lean_dec(v___x_6771_);
                                v___x_6774_ = leanh::lean_box(0);
                                v_isShared_6775_ = v_isSharedCheck_6779_;
                                state = 54;
                                continue;
                            }
                        }
                    }
                }
            }
            31 => {
                v___x_6591_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6591_, 0, v_a_6586_);
                if v_isShared_6589_ == 0 {
                    leanh::lean_ctor_set(v___x_6588_, 0, v___x_6591_);
                    v___x_6593_ = v___x_6588_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6594_, 0, v___x_6591_);
                    v___x_6593_ = v_reuseFailAlloc_6594_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_6593_;
            }
            33 => {
                leanh::lean_inc(v_goal_6406_);
                v___x_6611_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(v_goal_6406_, v_a_6586_, v___y_6600_, v___y_6601_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                if leanh::lean_obj_tag(v___x_6611_) == 0 {
                    v_a_6612_ = leanh::lean_ctor_get(v___x_6611_, 0);
                    leanh::lean_inc(v_a_6612_);
                    leanh::lean_dec_ref_known(v___x_6611_, 1);
                    if leanh::lean_obj_tag(v_a_6612_) == 1 {
                        leanh::lean_del_object(v___x_6588_);
                        leanh::lean_dec(v_a_6586_);
                        leanh::lean_dec(v_goal_6406_);
                        v_val_6613_ = leanh::lean_ctor_get(v_a_6612_, 0);
                        leanh::lean_inc(v_val_6613_);
                        leanh::lean_dec_ref_known(v_a_6612_, 1);
                        v_g_6425_ = v_val_6613_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_6612_);
                        leanh::lean_inc(v_goal_6406_);
                        v___x_6614_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(v_goal_6406_, v_a_6586_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                        if leanh::lean_obj_tag(v___x_6614_) == 0 {
                            v_a_6615_ = leanh::lean_ctor_get(v___x_6614_, 0);
                            leanh::lean_inc(v_a_6615_);
                            leanh::lean_dec_ref_known(v___x_6614_, 1);
                            if leanh::lean_obj_tag(v_a_6615_) == 1 {
                                leanh::lean_del_object(v___x_6588_);
                                leanh::lean_dec(v_a_6586_);
                                leanh::lean_dec(v_goal_6406_);
                                v_val_6616_ = leanh::lean_ctor_get(v_a_6615_, 0);
                                leanh::lean_inc(v_val_6616_);
                                leanh::lean_dec_ref_known(v_a_6615_, 1);
                                v_g_6425_ = v_val_6616_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_6615_);
                                leanh::lean_inc(v_goal_6406_);
                                v___x_6617_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(v_goal_6406_, v_a_6586_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                                if leanh::lean_obj_tag(v___x_6617_) == 0 {
                                    v_a_6618_ = leanh::lean_ctor_get(v___x_6617_, 0);
                                    leanh::lean_inc(v_a_6618_);
                                    leanh::lean_dec_ref_known(v___x_6617_, 1);
                                    if leanh::lean_obj_tag(v_a_6618_) == 1 {
                                        leanh::lean_del_object(v___x_6588_);
                                        leanh::lean_dec(v_a_6586_);
                                        leanh::lean_dec(v_goal_6406_);
                                        v_val_6619_ = leanh::lean_ctor_get(v_a_6618_, 0);
                                        leanh::lean_inc(v_val_6619_);
                                        leanh::lean_dec_ref_known(v_a_6618_, 1);
                                        v_g_6425_ = v_val_6619_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_6618_);
                                        leanh::lean_inc(v_goal_6406_);
                                        v___x_6620_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(v_goal_6406_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                                        if leanh::lean_obj_tag(v___x_6620_) == 0 {
                                            v_a_6621_ = leanh::lean_ctor_get(v___x_6620_, 0);
                                            leanh::lean_inc(v_a_6621_);
                                            leanh::lean_dec_ref_known(v___x_6620_, 1);
                                            if leanh::lean_obj_tag(v_a_6621_) == 1 {
                                                leanh::lean_del_object(v___x_6588_);
                                                leanh::lean_dec(v_a_6586_);
                                                leanh::lean_dec(v_goal_6406_);
                                                v_val_6622_ =
                                                    leanh::lean_ctor_get(v_a_6621_, 0);
                                                leanh::lean_inc(v_val_6622_);
                                                leanh::lean_dec_ref_known(v_a_6621_, 1);
                                                v_gs_6421_ = v_val_6622_;
                                                state = 1;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_a_6621_);
                                                leanh::lean_inc(v_a_6586_);
                                                v___x_6623_ =
                                                    l_Lean_Expr_cleanupAnnotations(v_a_6586_);
                                                v___x_6624_ = l_Lean_Expr_isApp(v___x_6623_);
                                                if v___x_6624_ == 0 {
                                                    leanh::lean_dec_ref(v___x_6623_);
                                                    leanh::lean_dec_ref(v_scope_6407_);
                                                    leanh::lean_dec(v_goal_6406_);
                                                    state = 31;
                                                    continue;
                                                } else {
                                                    v_arg_6625_ =
                                                        leanh::lean_ctor_get(v___x_6623_, 1);
                                                    leanh::lean_inc_ref(v_arg_6625_);
                                                    v___x_6626_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_6623_,
                                                    );
                                                    v___x_6627_ = l_Lean_Expr_isApp(v___x_6626_);
                                                    if v___x_6627_ == 0 {
                                                        leanh::lean_dec_ref(v___x_6626_);
                                                        leanh::lean_dec_ref(v_arg_6625_);
                                                        leanh::lean_dec_ref(v_scope_6407_);
                                                        leanh::lean_dec(v_goal_6406_);
                                                        state = 31;
                                                        continue;
                                                    } else {
                                                        v_arg_6628_ = leanh::lean_ctor_get(
                                                            v___x_6626_,
                                                            1,
                                                        );
                                                        leanh::lean_inc_ref(v_arg_6628_);
                                                        v___x_6629_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_6626_,
                                                            );
                                                        v___x_6630_ =
                                                            l_Lean_Expr_isApp(v___x_6629_);
                                                        if v___x_6630_ == 0 {
                                                            leanh::lean_dec_ref(v___x_6629_);
                                                            leanh::lean_dec_ref(v_arg_6628_);
                                                            leanh::lean_dec_ref(v_arg_6625_);
                                                            leanh::lean_dec_ref(
                                                                v_scope_6407_,
                                                            );
                                                            leanh::lean_dec(v_goal_6406_);
                                                            state = 31;
                                                            continue;
                                                        } else {
                                                            v_arg_6631_ =
                                                                leanh::lean_ctor_get(
                                                                    v___x_6629_,
                                                                    1,
                                                                );
                                                            leanh::lean_inc_ref(v_arg_6631_);
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
                                                                leanh::lean_dec_ref(
                                                                    v___x_6632_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_6631_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_6628_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_6625_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_scope_6407_,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_goal_6406_,
                                                                );
                                                                state = 31;
                                                                continue;
                                                            } else {
                                                                leanh::lean_del_object(
                                                                    v___x_6588_,
                                                                );
                                                                leanh::lean_dec(v_a_6586_);
                                                                leanh::lean_inc(
                                                                    v_goal_6406_,
                                                                );
                                                                v___x_6635_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(v_goal_6406_, v_arg_6625_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_6635_,
                                                                ) == 0
                                                                {
                                                                    v_a_6636_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_6635_,
                                                                            0,
                                                                        );
                                                                    leanh::lean_inc(
                                                                        v_a_6636_,
                                                                    );
                                                                    leanh::lean_dec_ref_known(v___x_6635_, 1);
                                                                    if leanh::lean_obj_tag(
                                                                        v_a_6636_,
                                                                    ) == 1
                                                                    {
                                                                        leanh::lean_dec_ref(
                                                                            v___x_6632_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_6631_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_6628_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_6625_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_goal_6406_,
                                                                        );
                                                                        v_val_6637_ = leanh::lean_ctor_get(v_a_6636_, 0);
                                                                        leanh::lean_inc(
                                                                            v_val_6637_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v_a_6636_, 1);
                                                                        v_g_6425_ = v_val_6637_;
                                                                        state = 2;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_dec(
                                                                            v_a_6636_,
                                                                        );
                                                                        leanh::lean_inc_ref(
                                                                            v_arg_6625_,
                                                                        );
                                                                        leanh::lean_inc_ref(
                                                                            v_arg_6628_,
                                                                        );
                                                                        leanh::lean_inc_ref(
                                                                            v_arg_6631_,
                                                                        );
                                                                        leanh::lean_inc_ref(
                                                                            v___x_6632_,
                                                                        );
                                                                        leanh::lean_inc(
                                                                            v_goal_6406_,
                                                                        );
                                                                        v___x_6638_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(v_goal_6406_, v___x_6632_, v_arg_6631_, v_arg_6628_, v_arg_6625_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                                                                        if leanh::lean_obj_tag(v___x_6638_) == 0 {
v_a_6639_ = leanh::lean_ctor_get(v___x_6638_, 0);
leanh::lean_inc(v_a_6639_);
leanh::lean_dec_ref_known(v___x_6638_, 1);
if leanh::lean_obj_tag(v_a_6639_) == 1 {
leanh::lean_dec_ref(v___x_6632_);
leanh::lean_dec_ref(v_arg_6631_);
leanh::lean_dec_ref(v_arg_6628_);
leanh::lean_dec_ref(v_arg_6625_);
leanh::lean_dec(v_goal_6406_);
v_val_6640_ = leanh::lean_ctor_get(v_a_6639_, 0);
leanh::lean_inc(v_val_6640_);
leanh::lean_dec_ref_known(v_a_6639_, 1);
v_g_6425_ = v_val_6640_;
state = 2; continue;
} else {
leanh::lean_dec(v_a_6639_);
v_dummy_6641_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1);
v_nargs_6642_ = l_Lean_Expr_getAppNumArgs(v_arg_6625_);
leanh::lean_inc(v_nargs_6642_);
v___x_6643_ = lean_mk_array(v_nargs_6642_, v_dummy_6641_);
v___x_6644_ = leanh::lean_unsigned_to_nat(1);
v___x_6645_ = lean_nat_sub(v_nargs_6642_, v___x_6644_);
leanh::lean_dec(v_nargs_6642_);
leanh::lean_inc_ref(v_arg_6625_);
v___x_6646_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__0(v_arg_6625_, v___x_6643_, v___x_6645_);
v_fst_6647_ = leanh::lean_ctor_get(v___x_6646_, 0);
v_snd_6648_ = leanh::lean_ctor_get(v___x_6646_, 1);
v_isSharedCheck_6717_ = (!leanh::lean_is_exclusive(v___x_6646_)) as u8;
if v_isSharedCheck_6717_ == 0 {
v___x_6650_ = v___x_6646_;
v_isShared_6651_ = v_isSharedCheck_6717_;
state = 34; continue;
} else {
leanh::lean_inc(v_snd_6648_);
leanh::lean_inc(v_fst_6647_);
leanh::lean_dec(v___x_6646_);
v___x_6650_ = leanh::lean_box(0);
v_isShared_6651_ = v_isSharedCheck_6717_;
state = 34; continue;
}
}
} else {
leanh::lean_dec_ref(v___x_6632_);
leanh::lean_dec_ref(v_arg_6631_);
leanh::lean_dec_ref(v_arg_6628_);
leanh::lean_dec_ref(v_arg_6625_);
leanh::lean_dec_ref(v_scope_6407_);
leanh::lean_dec(v_goal_6406_);
v_a_6718_ = leanh::lean_ctor_get(v___x_6638_, 0);
v_isSharedCheck_6725_ = (!leanh::lean_is_exclusive(v___x_6638_)) as u8;
if v_isSharedCheck_6725_ == 0 {
v___x_6720_ = v___x_6638_;
v_isShared_6721_ = v_isSharedCheck_6725_;
state = 42; continue;
} else {
leanh::lean_inc(v_a_6718_);
leanh::lean_dec(v___x_6638_);
v___x_6720_ = leanh::lean_box(0);
v_isShared_6721_ = v_isSharedCheck_6725_;
state = 42; continue;
}
}
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v___x_6632_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_6631_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_6628_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_6625_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_scope_6407_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_goal_6406_,
                                                                    );
                                                                    v_a_6726_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_6635_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_6733_ = (!leanh::lean_is_exclusive(v___x_6635_)) as u8;
                                                                    if v_isSharedCheck_6733_ == 0 {
                                                                        v___x_6728_ = v___x_6635_;
                                                                        v_isShared_6729_ =
                                                                            v_isSharedCheck_6733_;
                                                                        state = 44;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_6726_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_6635_,
                                                                        );
                                                                        v___x_6728_ =
                                                                            leanh::lean_box(
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
                                            leanh::lean_del_object(v___x_6588_);
                                            leanh::lean_dec(v_a_6586_);
                                            leanh::lean_dec_ref(v_scope_6407_);
                                            leanh::lean_dec(v_goal_6406_);
                                            v_a_6734_ = leanh::lean_ctor_get(v___x_6620_, 0);
                                            v_isSharedCheck_6741_ =
                                                (!leanh::lean_is_exclusive(v___x_6620_))
                                                    as u8;
                                            if v_isSharedCheck_6741_ == 0 {
                                                v___x_6736_ = v___x_6620_;
                                                v_isShared_6737_ = v_isSharedCheck_6741_;
                                                state = 46;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_6734_);
                                                leanh::lean_dec(v___x_6620_);
                                                v___x_6736_ = leanh::lean_box(0);
                                                v_isShared_6737_ = v_isSharedCheck_6741_;
                                                state = 46;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_6588_);
                                    leanh::lean_dec(v_a_6586_);
                                    leanh::lean_dec_ref(v_scope_6407_);
                                    leanh::lean_dec(v_goal_6406_);
                                    v_a_6742_ = leanh::lean_ctor_get(v___x_6617_, 0);
                                    v_isSharedCheck_6749_ =
                                        (!leanh::lean_is_exclusive(v___x_6617_)) as u8;
                                    if v_isSharedCheck_6749_ == 0 {
                                        v___x_6744_ = v___x_6617_;
                                        v_isShared_6745_ = v_isSharedCheck_6749_;
                                        state = 48;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6742_);
                                        leanh::lean_dec(v___x_6617_);
                                        v___x_6744_ = leanh::lean_box(0);
                                        v_isShared_6745_ = v_isSharedCheck_6749_;
                                        state = 48;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_6588_);
                            leanh::lean_dec(v_a_6586_);
                            leanh::lean_dec_ref(v_scope_6407_);
                            leanh::lean_dec(v_goal_6406_);
                            v_a_6750_ = leanh::lean_ctor_get(v___x_6614_, 0);
                            v_isSharedCheck_6757_ =
                                (!leanh::lean_is_exclusive(v___x_6614_)) as u8;
                            if v_isSharedCheck_6757_ == 0 {
                                v___x_6752_ = v___x_6614_;
                                v_isShared_6753_ = v_isSharedCheck_6757_;
                                state = 50;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6750_);
                                leanh::lean_dec(v___x_6614_);
                                v___x_6752_ = leanh::lean_box(0);
                                v_isShared_6753_ = v_isSharedCheck_6757_;
                                state = 50;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_6588_);
                    leanh::lean_dec(v_a_6586_);
                    leanh::lean_dec_ref(v_scope_6407_);
                    leanh::lean_dec(v_goal_6406_);
                    v_a_6758_ = leanh::lean_ctor_get(v___x_6611_, 0);
                    v_isSharedCheck_6765_ = (!leanh::lean_is_exclusive(v___x_6611_)) as u8;
                    if v_isSharedCheck_6765_ == 0 {
                        v___x_6760_ = v___x_6611_;
                        v_isShared_6761_ = v_isSharedCheck_6765_;
                        state = 52;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6758_);
                        leanh::lean_dec(v___x_6611_);
                        v___x_6760_ = leanh::lean_box(0);
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
                    leanh::lean_del_object(v___x_6650_);
                    leanh::lean_dec(v_snd_6648_);
                    leanh::lean_dec(v_fst_6647_);
                    leanh::lean_inc_ref(v_arg_6625_);
                    v___x_6654_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySolveSPredEntails(v_goal_6406_, v___x_6632_, v_arg_6631_, v_arg_6628_, v_arg_6625_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
                    leanh::lean_dec_ref(v___x_6632_);
                    if leanh::lean_obj_tag(v___x_6654_) == 0 {
                        v_a_6655_ = leanh::lean_ctor_get(v___x_6654_, 0);
                        v_isSharedCheck_6664_ =
                            (!leanh::lean_is_exclusive(v___x_6654_)) as u8;
                        if v_isSharedCheck_6664_ == 0 {
                            v___x_6657_ = v___x_6654_;
                            v_isShared_6658_ = v_isSharedCheck_6664_;
                            state = 35;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6655_);
                            leanh::lean_dec(v___x_6654_);
                            v___x_6657_ = leanh::lean_box(0);
                            v_isShared_6658_ = v_isSharedCheck_6664_;
                            state = 35;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_6625_);
                        leanh::lean_dec_ref(v_scope_6407_);
                        v_a_6665_ = leanh::lean_ctor_get(v___x_6654_, 0);
                        v_isSharedCheck_6672_ =
                            (!leanh::lean_is_exclusive(v___x_6654_)) as u8;
                        if v_isSharedCheck_6672_ == 0 {
                            v___x_6667_ = v___x_6654_;
                            v_isShared_6668_ = v_isSharedCheck_6672_;
                            state = 37;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6665_);
                            leanh::lean_dec(v___x_6654_);
                            v___x_6667_ = leanh::lean_box(0);
                            v_isShared_6668_ = v_isSharedCheck_6672_;
                            state = 37;
                            continue;
                        }
                    }
                } else {
                    v___x_6673_ = l_Lean_instInhabitedExpr;
                    v___x_6674_ = leanh::lean_unsigned_to_nat(2);
                    v___x_6675_ = lean_array_get_borrowed(v___x_6673_, v_snd_6648_, v___x_6674_);
                    leanh::lean_inc(v___x_6675_);
                    v___x_6676_ = l_Lean_Expr_cleanupAnnotations(v___x_6675_);
                    v___x_6677_ = l_Lean_Expr_isApp(v___x_6676_);
                    if v___x_6677_ == 0 {
                        leanh::lean_dec_ref(v___x_6676_);
                        leanh::lean_del_object(v___x_6650_);
                        leanh::lean_dec(v_snd_6648_);
                        leanh::lean_dec(v_fst_6647_);
                        leanh::lean_dec_ref(v___x_6632_);
                        leanh::lean_dec_ref(v_arg_6631_);
                        leanh::lean_dec_ref(v_arg_6628_);
                        leanh::lean_dec_ref(v_scope_6407_);
                        leanh::lean_dec(v_goal_6406_);
                        v___y_6431_ = v_arg_6625_;
                        state = 3;
                        continue;
                    } else {
                        v_arg_6678_ = leanh::lean_ctor_get(v___x_6676_, 1);
                        leanh::lean_inc_ref(v_arg_6678_);
                        v___x_6679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6676_);
                        v___x_6680_ = l_Lean_Expr_isApp(v___x_6679_);
                        if v___x_6680_ == 0 {
                            leanh::lean_dec_ref(v___x_6679_);
                            leanh::lean_dec_ref(v_arg_6678_);
                            leanh::lean_del_object(v___x_6650_);
                            leanh::lean_dec(v_snd_6648_);
                            leanh::lean_dec(v_fst_6647_);
                            leanh::lean_dec_ref(v___x_6632_);
                            leanh::lean_dec_ref(v_arg_6631_);
                            leanh::lean_dec_ref(v_arg_6628_);
                            leanh::lean_dec_ref(v_scope_6407_);
                            leanh::lean_dec(v_goal_6406_);
                            v___y_6431_ = v_arg_6625_;
                            state = 3;
                            continue;
                        } else {
                            v_arg_6681_ = leanh::lean_ctor_get(v___x_6679_, 1);
                            leanh::lean_inc_ref(v_arg_6681_);
                            v___x_6682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6679_);
                            v___x_6683_ = l_Lean_Expr_isApp(v___x_6682_);
                            if v___x_6683_ == 0 {
                                leanh::lean_dec_ref(v___x_6682_);
                                leanh::lean_dec_ref(v_arg_6681_);
                                leanh::lean_dec_ref(v_arg_6678_);
                                leanh::lean_del_object(v___x_6650_);
                                leanh::lean_dec(v_snd_6648_);
                                leanh::lean_dec(v_fst_6647_);
                                leanh::lean_dec_ref(v___x_6632_);
                                leanh::lean_dec_ref(v_arg_6631_);
                                leanh::lean_dec_ref(v_arg_6628_);
                                leanh::lean_dec_ref(v_scope_6407_);
                                leanh::lean_dec(v_goal_6406_);
                                v___y_6431_ = v_arg_6625_;
                                state = 3;
                                continue;
                            } else {
                                v_arg_6684_ = leanh::lean_ctor_get(v___x_6682_, 1);
                                leanh::lean_inc_ref(v_arg_6684_);
                                v___x_6685_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6682_);
                                v___x_6686_ = l_Lean_Expr_isApp(v___x_6685_);
                                if v___x_6686_ == 0 {
                                    leanh::lean_dec_ref(v___x_6685_);
                                    leanh::lean_dec_ref(v_arg_6684_);
                                    leanh::lean_dec_ref(v_arg_6681_);
                                    leanh::lean_dec_ref(v_arg_6678_);
                                    leanh::lean_del_object(v___x_6650_);
                                    leanh::lean_dec(v_snd_6648_);
                                    leanh::lean_dec(v_fst_6647_);
                                    leanh::lean_dec_ref(v___x_6632_);
                                    leanh::lean_dec_ref(v_arg_6631_);
                                    leanh::lean_dec_ref(v_arg_6628_);
                                    leanh::lean_dec_ref(v_scope_6407_);
                                    leanh::lean_dec(v_goal_6406_);
                                    v___y_6431_ = v_arg_6625_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_arg_6687_ = leanh::lean_ctor_get(v___x_6685_, 1);
                                    leanh::lean_inc_ref(v_arg_6687_);
                                    v___x_6688_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6685_);
                                    v___x_6689_ = l_Lean_Expr_isApp(v___x_6688_);
                                    if v___x_6689_ == 0 {
                                        leanh::lean_dec_ref(v___x_6688_);
                                        leanh::lean_dec_ref(v_arg_6687_);
                                        leanh::lean_dec_ref(v_arg_6684_);
                                        leanh::lean_dec_ref(v_arg_6681_);
                                        leanh::lean_dec_ref(v_arg_6678_);
                                        leanh::lean_del_object(v___x_6650_);
                                        leanh::lean_dec(v_snd_6648_);
                                        leanh::lean_dec(v_fst_6647_);
                                        leanh::lean_dec_ref(v___x_6632_);
                                        leanh::lean_dec_ref(v_arg_6631_);
                                        leanh::lean_dec_ref(v_arg_6628_);
                                        leanh::lean_dec_ref(v_scope_6407_);
                                        leanh::lean_dec(v_goal_6406_);
                                        v___y_6431_ = v_arg_6625_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v_arg_6690_ = leanh::lean_ctor_get(v___x_6688_, 1);
                                        leanh::lean_inc_ref(v_arg_6690_);
                                        v___x_6691_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_6688_);
                                        v___x_6692_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7;
                                        v___x_6693_ =
                                            l_Lean_Expr_isConstOf(v___x_6691_, v___x_6692_);
                                        if v___x_6693_ == 0 {
                                            leanh::lean_dec_ref(v___x_6691_);
                                            leanh::lean_dec_ref(v_arg_6690_);
                                            leanh::lean_dec_ref(v_arg_6687_);
                                            leanh::lean_dec_ref(v_arg_6684_);
                                            leanh::lean_dec_ref(v_arg_6681_);
                                            leanh::lean_dec_ref(v_arg_6678_);
                                            leanh::lean_del_object(v___x_6650_);
                                            leanh::lean_dec(v_snd_6648_);
                                            leanh::lean_dec(v_fst_6647_);
                                            leanh::lean_dec_ref(v___x_6632_);
                                            leanh::lean_dec_ref(v_arg_6631_);
                                            leanh::lean_dec_ref(v_arg_6628_);
                                            leanh::lean_dec_ref(v_scope_6407_);
                                            leanh::lean_dec(v_goal_6406_);
                                            v___y_6431_ = v_arg_6625_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref(v_arg_6625_);
                                            v_options_6694_ =
                                                leanh::lean_ctor_get(v___y_6609_, 2);
                                            v_inheritedTraceOptions_6695_ =
                                                leanh::lean_ctor_get(v___y_6609_, 13);
                                            v_hasTrace_6696_ = leanh::lean_ctor_get_uint8(
                                                v_options_6694_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 1)
                                                    as u32,
                                            );
                                            v___x_6697_ = leanh::lean_unsigned_to_nat(4);
                                            v___x_6698_ = lean_array_get_size(v_snd_6648_);
                                            v___x_6699_ = l_Array_extract___redArg(
                                                v_snd_6648_,
                                                v___x_6697_,
                                                v___x_6698_,
                                            );
                                            v___x_6700_ = l_Lean_Expr_getAppFn(v_arg_6678_);
                                            if v_hasTrace_6696_ == 0 {
                                                leanh::lean_del_object(v___x_6650_);
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
                                                v___x_6701_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
                                                v___x_6702_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6695_, v_options_6694_, v___x_6701_);
                                                if v___x_6702_ == 0 {
                                                    leanh::lean_del_object(v___x_6650_);
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
                                                    v___x_6703_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9);
                                                    leanh::lean_inc_ref(v_arg_6678_);
                                                    v___x_6704_ =
                                                        l_Lean_MessageData_ofExpr(v_arg_6678_);
                                                    if v_isShared_6651_ == 0 {
                                                        leanh::lean_ctor_set_tag(
                                                            v___x_6650_,
                                                            7,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_6650_,
                                                            1,
                                                            v___x_6704_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_6650_,
                                                            0,
                                                            v___x_6703_,
                                                        );
                                                        v___x_6706_ = v___x_6650_;
                                                        state = 39;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_6716_ =
                                                            leanh::lean_alloc_ctor(
                                                                7,
                                                                2,
                                                                (0) as u32,
                                                            );
                                                        leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_6716_,
                                                            0,
                                                            v___x_6703_,
                                                        );
                                                        leanh::lean_ctor_set(
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
                if leanh::lean_obj_tag(v_a_6655_) == 1 {
                    leanh::lean_del_object(v___x_6657_);
                    leanh::lean_dec_ref(v_arg_6625_);
                    v_val_6659_ = leanh::lean_ctor_get(v_a_6655_, 0);
                    leanh::lean_inc(v_val_6659_);
                    leanh::lean_dec_ref_known(v_a_6655_, 1);
                    v_gs_6421_ = v_val_6659_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_6655_);
                    leanh::lean_dec_ref(v_scope_6407_);
                    v___x_6660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6660_, 0, v_arg_6625_);
                    if v_isShared_6658_ == 0 {
                        leanh::lean_ctor_set(v___x_6657_, 0, v___x_6660_);
                        v___x_6662_ = v___x_6657_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_6663_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6663_, 0, v___x_6660_);
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
                    v_reuseFailAlloc_6671_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6671_, 0, v_a_6665_);
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
                if leanh::lean_obj_tag(v___x_6707_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6707_, 1);
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
                    leanh::lean_dec_ref(v___x_6700_);
                    leanh::lean_dec_ref(v___x_6699_);
                    leanh::lean_dec_ref(v___x_6691_);
                    leanh::lean_dec_ref(v_arg_6690_);
                    leanh::lean_dec_ref(v_arg_6687_);
                    leanh::lean_dec_ref(v_arg_6684_);
                    leanh::lean_dec_ref(v_arg_6681_);
                    leanh::lean_dec_ref(v_arg_6678_);
                    leanh::lean_dec(v_snd_6648_);
                    leanh::lean_dec(v_fst_6647_);
                    leanh::lean_dec_ref(v___x_6632_);
                    leanh::lean_dec_ref(v_arg_6631_);
                    leanh::lean_dec_ref(v_arg_6628_);
                    leanh::lean_dec_ref(v_scope_6407_);
                    leanh::lean_dec(v_goal_6406_);
                    v_a_6708_ = leanh::lean_ctor_get(v___x_6707_, 0);
                    v_isSharedCheck_6715_ = (!leanh::lean_is_exclusive(v___x_6707_)) as u8;
                    if v_isSharedCheck_6715_ == 0 {
                        v___x_6710_ = v___x_6707_;
                        v_isShared_6711_ = v_isSharedCheck_6715_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6708_);
                        leanh::lean_dec(v___x_6707_);
                        v___x_6710_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_6714_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6714_, 0, v_a_6708_);
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
                    v_reuseFailAlloc_6724_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 0, v_a_6718_);
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
                    v_reuseFailAlloc_6732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 0, v_a_6726_);
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
                    v_reuseFailAlloc_6740_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6740_, 0, v_a_6734_);
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
                    v_reuseFailAlloc_6748_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6748_, 0, v_a_6742_);
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
                    v_reuseFailAlloc_6756_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6756_, 0, v_a_6750_);
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
                    v_reuseFailAlloc_6764_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6764_, 0, v_a_6758_);
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
                    v_reuseFailAlloc_6778_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6778_, 0, v_a_6772_);
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
                    v_reuseFailAlloc_6787_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6787_, 0, v_a_6781_);
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
    mut v_goal_6789_: *mut leanh::LeanObject,
    mut v_scope_6790_: *mut leanh::LeanObject,
    mut v___y_6791_: *mut leanh::LeanObject,
    mut v___y_6792_: *mut leanh::LeanObject,
    mut v___y_6793_: *mut leanh::LeanObject,
    mut v___y_6794_: *mut leanh::LeanObject,
    mut v___y_6795_: *mut leanh::LeanObject,
    mut v___y_6796_: *mut leanh::LeanObject,
    mut v___y_6797_: *mut leanh::LeanObject,
    mut v___y_6798_: *mut leanh::LeanObject,
    mut v___y_6799_: *mut leanh::LeanObject,
    mut v___y_6800_: *mut leanh::LeanObject,
    mut v___y_6801_: *mut leanh::LeanObject,
    mut v___y_6802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6803_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_6801_);
    leanh::lean_dec_ref(v___y_6800_);
    leanh::lean_dec(v___y_6799_);
    leanh::lean_dec_ref(v___y_6798_);
    leanh::lean_dec(v___y_6797_);
    leanh::lean_dec_ref(v___y_6796_);
    leanh::lean_dec(v___y_6795_);
    leanh::lean_dec_ref(v___y_6794_);
    leanh::lean_dec(v___y_6793_);
    leanh::lean_dec(v___y_6792_);
    leanh::lean_dec_ref(v___y_6791_);
    return v_res_6803_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(
    mut v_scope_6804_: *mut leanh::LeanObject,
    mut v_goal_6805_: *mut leanh::LeanObject,
    mut v_a_6806_: *mut leanh::LeanObject,
    mut v_a_6807_: *mut leanh::LeanObject,
    mut v_a_6808_: *mut leanh::LeanObject,
    mut v_a_6809_: *mut leanh::LeanObject,
    mut v_a_6810_: *mut leanh::LeanObject,
    mut v_a_6811_: *mut leanh::LeanObject,
    mut v_a_6812_: *mut leanh::LeanObject,
    mut v_a_6813_: *mut leanh::LeanObject,
    mut v_a_6814_: *mut leanh::LeanObject,
    mut v_a_6815_: *mut leanh::LeanObject,
    mut v_a_6816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_goal_6805_);
    v___f_6818_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed as *mut core::ffi::c_void,
        14,
        2,
    );
    leanh::lean_closure_set(v___f_6818_, 0, v_goal_6805_);
    leanh::lean_closure_set(v___f_6818_, 1, v_scope_6804_);
    v___x_6819_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_goal_6805_, v___f_6818_, v_a_6806_, v_a_6807_, v_a_6808_, v_a_6809_, v_a_6810_, v_a_6811_, v_a_6812_, v_a_6813_, v_a_6814_, v_a_6815_, v_a_6816_);
    return v___x_6819_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(
    mut v_scope_6820_: *mut leanh::LeanObject,
    mut v_goal_6821_: *mut leanh::LeanObject,
    mut v_a_6822_: *mut leanh::LeanObject,
    mut v_a_6823_: *mut leanh::LeanObject,
    mut v_a_6824_: *mut leanh::LeanObject,
    mut v_a_6825_: *mut leanh::LeanObject,
    mut v_a_6826_: *mut leanh::LeanObject,
    mut v_a_6827_: *mut leanh::LeanObject,
    mut v_a_6828_: *mut leanh::LeanObject,
    mut v_a_6829_: *mut leanh::LeanObject,
    mut v_a_6830_: *mut leanh::LeanObject,
    mut v_a_6831_: *mut leanh::LeanObject,
    mut v_a_6832_: *mut leanh::LeanObject,
    mut v_a_6833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6834_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_6832_);
    leanh::lean_dec_ref(v_a_6831_);
    leanh::lean_dec(v_a_6830_);
    leanh::lean_dec_ref(v_a_6829_);
    leanh::lean_dec(v_a_6828_);
    leanh::lean_dec_ref(v_a_6827_);
    leanh::lean_dec(v_a_6826_);
    leanh::lean_dec_ref(v_a_6825_);
    leanh::lean_dec(v_a_6824_);
    leanh::lean_dec(v_a_6823_);
    leanh::lean_dec_ref(v_a_6822_);
    return v_res_6834_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
}
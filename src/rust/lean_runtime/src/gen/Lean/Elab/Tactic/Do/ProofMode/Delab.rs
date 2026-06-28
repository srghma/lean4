// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Delab
// Imports: Lean.Elab.Tactic.Do.ProofMode.MGoal
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Data::Repr::l_Nat_toSuperscriptString;
use crate::r#gen::Init::Meta::Defs::{lean_mk_syntax_ident, lean_name_append_after};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesIdent,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_addMacroScope,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_String_toRawSubstring_x27, l_instInhabitedOfMonad___redArg,
    lean_erase_macro_scopes,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal, l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppNumArgs,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Basic::{
    l_Lean_PrettyPrinter_Delaborator_delab___boxed,
    l_Lean_PrettyPrinter_Delaborator_delabAttribute,
    l_Lean_PrettyPrinter_Delaborator_failure___redArg,
};
use crate::r#gen::Lean::SubExpr::l_Lean_SubExpr_Pos_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_panic_fn_borrowed,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__0_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__1_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 46, 119, 105, 116, 104, 77, 68, 97, 116, 97, 69, 120, 112, 114, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__2_value) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 101, 114, 109, 83, 112, 114, 101, 100, 40, 95, 41, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__2_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__2_value) as *mut LeanObject,13979102795498516556 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__7_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__7_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__9_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__9_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__9_value) as *mut LeanObject,14296711813398647265 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__10_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11_value) as *mut LeanObject,7043493786777132025 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__13_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__13_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__13_value) as *mut LeanObject,5346268661279150583 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__15_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__15_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__15_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__17_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__17_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__17_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__20_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__20_value) as *mut LeanObject;
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__22_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 80, 114, 101, 100, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__22_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__23_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__23_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__22_value) as *mut LeanObject,13332341187416043682 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__23_value) as *mut LeanObject,611622866940524098 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__25_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__25_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__26_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__26_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__26_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__28_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__28_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__30_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__30_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__31_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 99, 114, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__31_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__31_value) as *mut LeanObject,18105168627502861736 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__33_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__33_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__34_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__34: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__34_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__35_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__34_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__35: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__35_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__36_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__35_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__36: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__36_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__37_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__33_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__36_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__37: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__37_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__38_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__30_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__37_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__38: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__38_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__39_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__28_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__38_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__39: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__39_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__25_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__39_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__42_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__42: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__42_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__42_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__45_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__45: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__45_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__45_value) as *mut LeanObject,16077784126176397009 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value) as *mut LeanObject;
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__48_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__48: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__48_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__49_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__49: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__49_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__50_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__50: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__50_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__51_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__51: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__51_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_delab___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 103, 111, 97, 108, 72, 121, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value) as *mut LeanObject,1041404937882640577 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__2_value) as *mut LeanObject,1824513113201743363 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 156, 157, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__3_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__4_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 2, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__3_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__5_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 103, 111, 97, 108, 83, 116, 120, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value) as *mut LeanObject,1041404937882640577 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__5_value) as *mut LeanObject,2380567982751280064 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__7_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 2, m_data: [226, 138, 162, 226, 130, 155, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__1_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [77, 71, 111, 97, 108, 69, 110, 116, 97, 105, 108, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__0_value) as *mut LeanObject,2922699235639139989 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value) as *mut LeanObject,4831492069241297846 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value) as *mut LeanObject,2324254554473108299 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value) as *mut LeanObject,8942478639253722007 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__1_value) as *mut LeanObject,413037054110963389 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__3_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__6_value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value) as *mut LeanObject,5409699204079762053 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value) as *mut LeanObject,14659826576719934041 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__10_value) as *mut LeanObject,4071431237389361899 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__12_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [68, 101, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__12_value) as *mut LeanObject,1877758324957780182 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__13_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,8376554877021480703 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__14_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value) as *mut LeanObject,4013241711507038258 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__6_value) as *mut LeanObject,9291356050048015696 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__16_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value) as *mut LeanObject,9240637668200542125 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__17_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value) as *mut LeanObject,11162151232179256673 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__18_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__10_value) as *mut LeanObject,15205849050163241299 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__20_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 108, 97, 98, 77, 71, 111, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__19_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__20_value) as *mut LeanObject,818805323480328803 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [77, 71, 111, 97, 108, 72, 121, 112, 77, 97, 114, 107, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__0_value) as *mut LeanObject,2922699235639139989 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value) as *mut LeanObject,4831492069241297846 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value) as *mut LeanObject,2324254554473108299 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value) as *mut LeanObject,8942478639253722007 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__0_value) as *mut LeanObject,8095812656016205994 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__2_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 101, 108, 97, 98, 72, 121, 112, 77, 97, 114, 107, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__19_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__2_value) as *mut LeanObject,18336767047052267325 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__3_value) as *mut LeanObject;
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(
    mut v___y_944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subExpr_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    v_subExpr_946_ = lean_ctor_get(v___y_944_, 3);
    v_expr_947_ = lean_ctor_get(v_subExpr_946_, 0);
    lean_inc_ref(v_expr_947_);
    v___x_948_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_948_, 0, v_expr_947_);
    return v___x_948_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg___boxed(
    mut v___y_949_: *mut LeanObject,
    mut v___y_950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_951_: *mut LeanObject = core::ptr::null_mut();
    v_res_951_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_949_);
    lean_dec_ref(v___y_949_);
    return v_res_951_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0(
    mut v___y_952_: *mut LeanObject,
    mut v___y_953_: *mut LeanObject,
    mut v___y_954_: *mut LeanObject,
    mut v___y_955_: *mut LeanObject,
    mut v___y_956_: *mut LeanObject,
    mut v___y_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    v___x_959_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_952_);
    return v___x_959_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___boxed(
    mut v___y_960_: *mut LeanObject,
    mut v___y_961_: *mut LeanObject,
    mut v___y_962_: *mut LeanObject,
    mut v___y_963_: *mut LeanObject,
    mut v___y_964_: *mut LeanObject,
    mut v___y_965_: *mut LeanObject,
    mut v___y_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_967_: *mut LeanObject = core::ptr::null_mut();
    v_res_967_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0(v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
    lean_dec(v___y_965_);
    lean_dec_ref(v___y_964_);
    lean_dec(v___y_963_);
    lean_dec_ref(v___y_962_);
    lean_dec(v___y_961_);
    lean_dec_ref(v___y_960_);
    return v_res_967_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(
    mut v_child_968_: *mut LeanObject,
    mut v_childIdx_969_: *mut LeanObject,
    mut v_x_970_: *mut LeanObject,
    mut v___y_971_: *mut LeanObject,
    mut v___y_972_: *mut LeanObject,
    mut v___y_973_: *mut LeanObject,
    mut v___y_974_: *mut LeanObject,
    mut v___y_975_: *mut LeanObject,
    mut v___y_976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subExpr_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_optionsPerPos_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inPattern_982_: u8 = 0;
    let mut v_depth_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctxInitIndices_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    v_subExpr_978_ = lean_ctor_get(v___y_971_, 3);
    v_optionsPerPos_979_ = lean_ctor_get(v___y_971_, 0);
    v_currNamespace_980_ = lean_ctor_get(v___y_971_, 1);
    v_openDecls_981_ = lean_ctor_get(v___y_971_, 2);
    v_inPattern_982_ = lean_ctor_get_uint8(
        v___y_971_,
        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
    );
    v_depth_983_ = lean_ctor_get(v___y_971_, 4);
    v_lctxInitIndices_984_ = lean_ctor_get(v___y_971_, 5);
    v_pos_985_ = lean_ctor_get(v_subExpr_978_, 1);
    v___x_986_ = l_Lean_SubExpr_Pos_push(v_pos_985_, v_childIdx_969_);
    v___x_987_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_987_, 0, v_child_968_);
    lean_ctor_set(v___x_987_, 1, v___x_986_);
    lean_inc(v_lctxInitIndices_984_);
    lean_inc(v_depth_983_);
    lean_inc(v_openDecls_981_);
    lean_inc(v_currNamespace_980_);
    lean_inc(v_optionsPerPos_979_);
    v___x_988_ = lean_alloc_ctor(0, 6, (1) as u32);
    lean_ctor_set(v___x_988_, 0, v_optionsPerPos_979_);
    lean_ctor_set(v___x_988_, 1, v_currNamespace_980_);
    lean_ctor_set(v___x_988_, 2, v_openDecls_981_);
    lean_ctor_set(v___x_988_, 3, v___x_987_);
    lean_ctor_set(v___x_988_, 4, v_depth_983_);
    lean_ctor_set(v___x_988_, 5, v_lctxInitIndices_984_);
    lean_ctor_set_uint8(
        v___x_988_,
        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
        v_inPattern_982_,
    );
    lean_inc(v___y_976_);
    lean_inc_ref(v___y_975_);
    lean_inc(v___y_974_);
    lean_inc_ref(v___y_973_);
    lean_inc(v___y_972_);
    v___x_989_ = lean_apply_7(
        v_x_970_,
        v___x_988_,
        v___y_972_,
        v___y_973_,
        v___y_974_,
        v___y_975_,
        v___y_976_,
        lean_box(0),
    );
    return v___x_989_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg___boxed(
    mut v_child_990_: *mut LeanObject,
    mut v_childIdx_991_: *mut LeanObject,
    mut v_x_992_: *mut LeanObject,
    mut v___y_993_: *mut LeanObject,
    mut v___y_994_: *mut LeanObject,
    mut v___y_995_: *mut LeanObject,
    mut v___y_996_: *mut LeanObject,
    mut v___y_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1000_: *mut LeanObject = core::ptr::null_mut();
    v_res_1000_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v_child_990_, v_childIdx_991_, v_x_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
    lean_dec(v___y_998_);
    lean_dec_ref(v___y_997_);
    lean_dec(v___y_996_);
    lean_dec_ref(v___y_995_);
    lean_dec(v___y_994_);
    lean_dec_ref(v___y_993_);
    return v_res_1000_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(
    mut v_x_1001_: *mut LeanObject,
    mut v___y_1002_: *mut LeanObject,
    mut v___y_1003_: *mut LeanObject,
    mut v___y_1004_: *mut LeanObject,
    mut v___y_1005_: *mut LeanObject,
    mut v___y_1006_: *mut LeanObject,
    mut v___y_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    v___x_1009_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_1002_);
    v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
    lean_inc(v_a_1010_);
    lean_dec_ref(v___x_1009_);
    v___x_1011_ = l_Lean_Expr_appArg_x21(v_a_1010_);
    lean_dec(v_a_1010_);
    v___x_1012_ = lean_unsigned_to_nat(1);
    v___x_1013_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v___x_1011_, v___x_1012_, v_x_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
    return v___x_1013_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg___boxed(
    mut v_x_1014_: *mut LeanObject,
    mut v___y_1015_: *mut LeanObject,
    mut v___y_1016_: *mut LeanObject,
    mut v___y_1017_: *mut LeanObject,
    mut v___y_1018_: *mut LeanObject,
    mut v___y_1019_: *mut LeanObject,
    mut v___y_1020_: *mut LeanObject,
    mut v___y_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1022_: *mut LeanObject = core::ptr::null_mut();
    v_res_1022_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v_x_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
    lean_dec(v___y_1020_);
    lean_dec_ref(v___y_1019_);
    lean_dec(v___y_1018_);
    lean_dec_ref(v___y_1017_);
    lean_dec(v___y_1016_);
    lean_dec_ref(v___y_1015_);
    return v_res_1022_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4(
    mut v_00_u03b1_1023_: *mut LeanObject,
    mut v_x_1024_: *mut LeanObject,
    mut v___y_1025_: *mut LeanObject,
    mut v___y_1026_: *mut LeanObject,
    mut v___y_1027_: *mut LeanObject,
    mut v___y_1028_: *mut LeanObject,
    mut v___y_1029_: *mut LeanObject,
    mut v___y_1030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    v___x_1032_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v_x_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
    return v___x_1032_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___boxed(
    mut v_00_u03b1_1033_: *mut LeanObject,
    mut v_x_1034_: *mut LeanObject,
    mut v___y_1035_: *mut LeanObject,
    mut v___y_1036_: *mut LeanObject,
    mut v___y_1037_: *mut LeanObject,
    mut v___y_1038_: *mut LeanObject,
    mut v___y_1039_: *mut LeanObject,
    mut v___y_1040_: *mut LeanObject,
    mut v___y_1041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1042_: *mut LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4(v_00_u03b1_1033_, v_x_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
    lean_dec(v___y_1040_);
    lean_dec_ref(v___y_1039_);
    lean_dec(v___y_1038_);
    lean_dec_ref(v___y_1037_);
    lean_dec(v___y_1036_);
    lean_dec_ref(v___y_1035_);
    return v_res_1042_;
}
pub unsafe fn _init_l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    v___x_1043_ = l_instMonadEIO(lean_box(0));
    return v___x_1043_;
}
pub unsafe fn l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(
    mut v_msg_1048_: *mut LeanObject,
    mut v___y_1049_: *mut LeanObject,
    mut v___y_1050_: *mut LeanObject,
    mut v___y_1051_: *mut LeanObject,
    mut v___y_1052_: *mut LeanObject,
    mut v___y_1053_: *mut LeanObject,
    mut v___y_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1061_: u8 = 0;
    let mut v_toFunctor_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1068_: u8 = 0;
    let mut v___f_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1085_: u8 = 0;
    let mut v_toFunctor_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1092_: u8 = 0;
    let mut v___f_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_37994__overap_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1113_: u8 = 0;
    let mut v_unused_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1115_: u8 = 0;
    let mut v_unused_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut v_unused_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1121_: u8 = 0;
    let mut v_unused_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1056_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0_once), _init_l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0);
                v___x_1057_ = l_StateRefT_x27_instMonad___redArg(v___x_1056_);
                v_toApplicative_1058_ = lean_ctor_get(v___x_1057_, 0);
                v_isSharedCheck_1121_ = (!lean_is_exclusive(v___x_1057_)) as u8;
                if v_isSharedCheck_1121_ == 0 {
                    v_unused_1122_ = lean_ctor_get(v___x_1057_, 1);
                    lean_dec(v_unused_1122_);
                    v___x_1060_ = v___x_1057_;
                    v_isShared_1061_ = v_isSharedCheck_1121_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1058_);
                    lean_dec(v___x_1057_);
                    v___x_1060_ = lean_box(0);
                    v_isShared_1061_ = v_isSharedCheck_1121_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1062_ = lean_ctor_get(v_toApplicative_1058_, 0);
                v_toSeq_1063_ = lean_ctor_get(v_toApplicative_1058_, 2);
                v_toSeqLeft_1064_ = lean_ctor_get(v_toApplicative_1058_, 3);
                v_toSeqRight_1065_ = lean_ctor_get(v_toApplicative_1058_, 4);
                v_isSharedCheck_1119_ = (!lean_is_exclusive(v_toApplicative_1058_)) as u8;
                if v_isSharedCheck_1119_ == 0 {
                    v_unused_1120_ = lean_ctor_get(v_toApplicative_1058_, 1);
                    lean_dec(v_unused_1120_);
                    v___x_1067_ = v_toApplicative_1058_;
                    v_isShared_1068_ = v_isSharedCheck_1119_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1065_);
                    lean_inc(v_toSeqLeft_1064_);
                    lean_inc(v_toSeq_1063_);
                    lean_inc(v_toFunctor_1062_);
                    lean_dec(v_toApplicative_1058_);
                    v___x_1067_ = lean_box(0);
                    v_isShared_1068_ = v_isSharedCheck_1119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1069_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__1;
                v___f_1070_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__2;
                lean_inc_ref(v_toFunctor_1062_);
                v___f_1071_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1071_, 0, v_toFunctor_1062_);
                v___f_1072_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1072_, 0, v_toFunctor_1062_);
                v___x_1073_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1073_, 0, v___f_1071_);
                lean_ctor_set(v___x_1073_, 1, v___f_1072_);
                v___f_1074_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1074_, 0, v_toSeqRight_1065_);
                v___f_1075_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1075_, 0, v_toSeqLeft_1064_);
                v___f_1076_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1076_, 0, v_toSeq_1063_);
                if v_isShared_1068_ == 0 {
                    lean_ctor_set(v___x_1067_, 4, v___f_1074_);
                    lean_ctor_set(v___x_1067_, 3, v___f_1075_);
                    lean_ctor_set(v___x_1067_, 2, v___f_1076_);
                    lean_ctor_set(v___x_1067_, 1, v___f_1069_);
                    lean_ctor_set(v___x_1067_, 0, v___x_1073_);
                    v___x_1078_ = v___x_1067_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1073_);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 1, v___f_1069_);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 2, v___f_1076_);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 3, v___f_1075_);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 4, v___f_1074_);
                    v___x_1078_ = v_reuseFailAlloc_1118_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1061_ == 0 {
                    lean_ctor_set(v___x_1060_, 1, v___f_1070_);
                    lean_ctor_set(v___x_1060_, 0, v___x_1078_);
                    v___x_1080_ = v___x_1060_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1078_);
                    lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___f_1070_);
                    v___x_1080_ = v_reuseFailAlloc_1117_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1081_ = l_StateRefT_x27_instMonad___redArg(v___x_1080_);
                v_toApplicative_1082_ = lean_ctor_get(v___x_1081_, 0);
                v_isSharedCheck_1115_ = (!lean_is_exclusive(v___x_1081_)) as u8;
                if v_isSharedCheck_1115_ == 0 {
                    v_unused_1116_ = lean_ctor_get(v___x_1081_, 1);
                    lean_dec(v_unused_1116_);
                    v___x_1084_ = v___x_1081_;
                    v_isShared_1085_ = v_isSharedCheck_1115_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1082_);
                    lean_dec(v___x_1081_);
                    v___x_1084_ = lean_box(0);
                    v_isShared_1085_ = v_isSharedCheck_1115_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1086_ = lean_ctor_get(v_toApplicative_1082_, 0);
                v_toSeq_1087_ = lean_ctor_get(v_toApplicative_1082_, 2);
                v_toSeqLeft_1088_ = lean_ctor_get(v_toApplicative_1082_, 3);
                v_toSeqRight_1089_ = lean_ctor_get(v_toApplicative_1082_, 4);
                v_isSharedCheck_1113_ = (!lean_is_exclusive(v_toApplicative_1082_)) as u8;
                if v_isSharedCheck_1113_ == 0 {
                    v_unused_1114_ = lean_ctor_get(v_toApplicative_1082_, 1);
                    lean_dec(v_unused_1114_);
                    v___x_1091_ = v_toApplicative_1082_;
                    v_isShared_1092_ = v_isSharedCheck_1113_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1089_);
                    lean_inc(v_toSeqLeft_1088_);
                    lean_inc(v_toSeq_1087_);
                    lean_inc(v_toFunctor_1086_);
                    lean_dec(v_toApplicative_1082_);
                    v___x_1091_ = lean_box(0);
                    v_isShared_1092_ = v_isSharedCheck_1113_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1093_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__3;
                v___f_1094_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__4;
                lean_inc_ref(v_toFunctor_1086_);
                v___f_1095_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1095_, 0, v_toFunctor_1086_);
                v___f_1096_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1096_, 0, v_toFunctor_1086_);
                v___x_1097_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1097_, 0, v___f_1095_);
                lean_ctor_set(v___x_1097_, 1, v___f_1096_);
                v___f_1098_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1098_, 0, v_toSeqRight_1089_);
                v___f_1099_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1099_, 0, v_toSeqLeft_1088_);
                v___f_1100_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1100_, 0, v_toSeq_1087_);
                if v_isShared_1092_ == 0 {
                    lean_ctor_set(v___x_1091_, 4, v___f_1098_);
                    lean_ctor_set(v___x_1091_, 3, v___f_1099_);
                    lean_ctor_set(v___x_1091_, 2, v___f_1100_);
                    lean_ctor_set(v___x_1091_, 1, v___f_1093_);
                    lean_ctor_set(v___x_1091_, 0, v___x_1097_);
                    v___x_1102_ = v___x_1091_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1097_);
                    lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___f_1093_);
                    lean_ctor_set(v_reuseFailAlloc_1112_, 2, v___f_1100_);
                    lean_ctor_set(v_reuseFailAlloc_1112_, 3, v___f_1099_);
                    lean_ctor_set(v_reuseFailAlloc_1112_, 4, v___f_1098_);
                    v___x_1102_ = v_reuseFailAlloc_1112_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1085_ == 0 {
                    lean_ctor_set(v___x_1084_, 1, v___f_1094_);
                    lean_ctor_set(v___x_1084_, 0, v___x_1102_);
                    v___x_1104_ = v___x_1084_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1102_);
                    lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___f_1094_);
                    v___x_1104_ = v_reuseFailAlloc_1111_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1105_ = l_StateRefT_x27_instMonad___redArg(v___x_1104_);
                v___x_1106_ = l_ReaderT_instMonad___redArg(v___x_1105_);
                v___x_1107_ = lean_box(0);
                v___x_1108_ = l_instInhabitedOfMonad___redArg(v___x_1106_, v___x_1107_);
                v___x_37994__overap_1109_ = lean_panic_fn_borrowed(v___x_1108_, v_msg_1048_);
                lean_dec(v___x_1108_);
                lean_inc(v___y_1054_);
                lean_inc_ref(v___y_1053_);
                lean_inc(v___y_1052_);
                lean_inc_ref(v___y_1051_);
                lean_inc(v___y_1050_);
                lean_inc_ref(v___y_1049_);
                v___x_1110_ = lean_apply_7(
                    v___x_37994__overap_1109_,
                    v___y_1049_,
                    v___y_1050_,
                    v___y_1051_,
                    v___y_1052_,
                    v___y_1053_,
                    v___y_1054_,
                    lean_box(0),
                );
                return v___x_1110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___boxed(
    mut v_msg_1123_: *mut LeanObject,
    mut v___y_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
    mut v___y_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1131_: *mut LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(v_msg_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
    lean_dec(v___y_1129_);
    lean_dec_ref(v___y_1128_);
    lean_dec(v___y_1127_);
    lean_dec_ref(v___y_1126_);
    lean_dec(v___y_1125_);
    lean_dec_ref(v___y_1124_);
    return v_res_1131_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    v___x_1135_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__2;
    v___x_1136_ = lean_unsigned_to_nat(33);
    v___x_1137_ = lean_unsigned_to_nat(114);
    v___x_1138_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__1;
    v___x_1139_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__0;
    v___x_1140_ = l_mkPanicMessageWithDecl(
        v___x_1139_,
        v___x_1138_,
        v___x_1137_,
        v___x_1136_,
        v___x_1135_,
    );
    return v___x_1140_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(
    mut v_x_1141_: *mut LeanObject,
    mut v___y_1142_: *mut LeanObject,
    mut v___y_1143_: *mut LeanObject,
    mut v___y_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut LeanObject = core::ptr::null_mut();
    v___x_1149_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_1142_);
    v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
    lean_inc(v_a_1150_);
    lean_dec_ref(v___x_1149_);
    if lean_obj_tag(v_a_1150_) == 10 {
        let mut v_subExpr_1151_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expr_1152_: *mut LeanObject = core::ptr::null_mut();
        let mut v_optionsPerPos_1153_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currNamespace_1154_: *mut LeanObject = core::ptr::null_mut();
        let mut v_openDecls_1155_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inPattern_1156_: u8 = 0;
        let mut v_depth_1157_: *mut LeanObject = core::ptr::null_mut();
        let mut v_lctxInitIndices_1158_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pos_1159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
        v_subExpr_1151_ = lean_ctor_get(v___y_1142_, 3);
        v_expr_1152_ = lean_ctor_get(v_a_1150_, 1);
        lean_inc_ref(v_expr_1152_);
        lean_dec_ref_known(v_a_1150_, 2);
        v_optionsPerPos_1153_ = lean_ctor_get(v___y_1142_, 0);
        v_currNamespace_1154_ = lean_ctor_get(v___y_1142_, 1);
        v_openDecls_1155_ = lean_ctor_get(v___y_1142_, 2);
        v_inPattern_1156_ = lean_ctor_get_uint8(
            v___y_1142_,
            (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
        );
        v_depth_1157_ = lean_ctor_get(v___y_1142_, 4);
        v_lctxInitIndices_1158_ = lean_ctor_get(v___y_1142_, 5);
        v_pos_1159_ = lean_ctor_get(v_subExpr_1151_, 1);
        lean_inc(v_pos_1159_);
        v___x_1160_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1160_, 0, v_expr_1152_);
        lean_ctor_set(v___x_1160_, 1, v_pos_1159_);
        lean_inc(v_lctxInitIndices_1158_);
        lean_inc(v_depth_1157_);
        lean_inc(v_openDecls_1155_);
        lean_inc(v_currNamespace_1154_);
        lean_inc(v_optionsPerPos_1153_);
        v___x_1161_ = lean_alloc_ctor(0, 6, (1) as u32);
        lean_ctor_set(v___x_1161_, 0, v_optionsPerPos_1153_);
        lean_ctor_set(v___x_1161_, 1, v_currNamespace_1154_);
        lean_ctor_set(v___x_1161_, 2, v_openDecls_1155_);
        lean_ctor_set(v___x_1161_, 3, v___x_1160_);
        lean_ctor_set(v___x_1161_, 4, v_depth_1157_);
        lean_ctor_set(v___x_1161_, 5, v_lctxInitIndices_1158_);
        lean_ctor_set_uint8(
            v___x_1161_,
            (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
            v_inPattern_1156_,
        );
        lean_inc(v___y_1147_);
        lean_inc_ref(v___y_1146_);
        lean_inc(v___y_1145_);
        lean_inc_ref(v___y_1144_);
        lean_inc(v___y_1143_);
        v___x_1162_ = lean_apply_7(
            v_x_1141_,
            v___x_1161_,
            v___y_1143_,
            v___y_1144_,
            v___y_1145_,
            v___y_1146_,
            v___y_1147_,
            lean_box(0),
        );
        return v___x_1162_;
    } else {
        let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_1150_);
        lean_dec_ref(v_x_1141_);
        v___x_1163_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3);
        v___x_1164_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(v___x_1163_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
        return v___x_1164_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___boxed(
    mut v_x_1165_: *mut LeanObject,
    mut v___y_1166_: *mut LeanObject,
    mut v___y_1167_: *mut LeanObject,
    mut v___y_1168_: *mut LeanObject,
    mut v___y_1169_: *mut LeanObject,
    mut v___y_1170_: *mut LeanObject,
    mut v___y_1171_: *mut LeanObject,
    mut v___y_1172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1173_: *mut LeanObject = core::ptr::null_mut();
    v_res_1173_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(v_x_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
    lean_dec(v___y_1171_);
    lean_dec_ref(v___y_1170_);
    lean_dec(v___y_1169_);
    lean_dec_ref(v___y_1168_);
    lean_dec(v___y_1167_);
    lean_dec_ref(v___y_1166_);
    return v_res_1173_;
}
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21()
-> *mut LeanObject {
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__20;
    v___x_1217_ = l_String_toRawSubstring_x27(v___x_1216_);
    return v___x_1217_;
}
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47()
-> *mut LeanObject {
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    v___x_1274_ = l_Array_mkArray0(lean_box(0));
    return v___x_1274_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(
    mut v_x_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: u8 = 0;
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: u8 = 0;
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: u8 = 0;
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: u8 = 0;
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: u8 = 0;
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u8 = 0;
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: u8 = 0;
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_P_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1317_: u8 = 0;
    let mut v_ref_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1341_: u8 = 0;
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: u8 = 0;
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v_ref_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1375_: u8 = 0;
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v_ref_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_P_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1421_: u8 = 0;
    let mut v_ref_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1440_: u8 = 0;
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1282_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3;
                lean_inc(v_x_1279_);
                v___x_1283_ = l_Lean_Syntax_isOfKind(v_x_1279_, v___x_1282_);
                if v___x_1283_ == 0 {
                    v___x_1284_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8;
                    lean_inc(v_x_1279_);
                    v___x_1285_ = l_Lean_Syntax_isOfKind(v_x_1279_, v___x_1284_);
                    if v___x_1285_ == 0 {
                        v___x_1286_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__10;
                        lean_inc(v_x_1279_);
                        v___x_1287_ = l_Lean_Syntax_isOfKind(v_x_1279_, v___x_1286_);
                        if v___x_1287_ == 0 {
                            v___x_1288_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11;
                            v___x_1289_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12;
                            lean_inc(v_x_1279_);
                            v___x_1290_ = l_Lean_Syntax_isOfKind(v_x_1279_, v___x_1289_);
                            if v___x_1290_ == 0 {
                                v___x_1291_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14;
                                lean_inc(v_x_1279_);
                                v___x_1292_ = l_Lean_Syntax_isOfKind(v_x_1279_, v___x_1291_);
                                if v___x_1292_ == 0 {
                                    v___x_1293_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_1293_, 0, v_x_1279_);
                                    return v___x_1293_;
                                } else {
                                    v___x_1294_ = lean_unsigned_to_nat(0);
                                    v___x_1295_ = l_Lean_Syntax_getArg(v_x_1279_, v___x_1294_);
                                    v___x_1296_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16;
                                    lean_inc(v___x_1295_);
                                    v___x_1297_ = l_Lean_Syntax_isOfKind(v___x_1295_, v___x_1296_);
                                    if v___x_1297_ == 0 {
                                        lean_dec(v___x_1295_);
                                        v___x_1298_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v___x_1298_, 0, v_x_1279_);
                                        return v___x_1298_;
                                    } else {
                                        v___x_1299_ = lean_unsigned_to_nat(1);
                                        v___x_1300_ =
                                            l_Lean_Syntax_getArg(v___x_1295_, v___x_1299_);
                                        lean_dec(v___x_1295_);
                                        v___x_1301_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18;
                                        lean_inc(v___x_1300_);
                                        v___x_1302_ =
                                            l_Lean_Syntax_isOfKind(v___x_1300_, v___x_1301_);
                                        if v___x_1302_ == 0 {
                                            lean_dec(v___x_1300_);
                                            v___x_1303_ = lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v___x_1303_, 0, v_x_1279_);
                                            return v___x_1303_;
                                        } else {
                                            v___x_1304_ =
                                                l_Lean_Syntax_getArg(v___x_1300_, v___x_1294_);
                                            lean_dec(v___x_1300_);
                                            v___x_1305_ = lean_box(0);
                                            v___x_1306_ = l_Lean_Syntax_matchesIdent(
                                                v___x_1304_,
                                                v___x_1305_,
                                            );
                                            lean_dec(v___x_1304_);
                                            if v___x_1306_ == 0 {
                                                v___x_1307_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(v___x_1307_, 0, v_x_1279_);
                                                return v___x_1307_;
                                            } else {
                                                v___x_1308_ = lean_unsigned_to_nat(3);
                                                v___x_1309_ =
                                                    l_Lean_Syntax_getArg(v_x_1279_, v___x_1308_);
                                                lean_inc(v___x_1309_);
                                                v___x_1310_ = l_Lean_Syntax_matchesNull(
                                                    v___x_1309_,
                                                    v___x_1299_,
                                                );
                                                if v___x_1310_ == 0 {
                                                    lean_dec(v___x_1309_);
                                                    v___x_1311_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(v___x_1311_, 0, v_x_1279_);
                                                    return v___x_1311_;
                                                } else {
                                                    v_P_1312_ = l_Lean_Syntax_getArg(
                                                        v_x_1279_,
                                                        v___x_1299_,
                                                    );
                                                    lean_dec(v_x_1279_);
                                                    v___x_1313_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_P_1312_, v___y_1280_);
                                                    if lean_obj_tag(v___x_1313_) == 0 {
                                                        v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
                                                        v_isSharedCheck_1341_ =
                                                            (!lean_is_exclusive(v___x_1313_)) as u8;
                                                        if v_isSharedCheck_1341_ == 0 {
                                                            v___x_1316_ = v___x_1313_;
                                                            v_isShared_1317_ =
                                                                v_isSharedCheck_1341_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_1314_);
                                                            lean_dec(v___x_1313_);
                                                            v___x_1316_ = lean_box(0);
                                                            v_isShared_1317_ =
                                                                v_isSharedCheck_1341_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec(v___x_1309_);
                                                        return v___x_1313_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_1342_ = lean_unsigned_to_nat(1);
                                v___x_1343_ = l_Lean_Syntax_getArg(v_x_1279_, v___x_1342_);
                                v___x_1344_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46;
                                lean_inc(v___x_1343_);
                                v___x_1345_ = l_Lean_Syntax_isOfKind(v___x_1343_, v___x_1344_);
                                if v___x_1345_ == 0 {
                                    lean_dec(v___x_1343_);
                                    v___x_1346_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_1346_, 0, v_x_1279_);
                                    return v___x_1346_;
                                } else {
                                    v___x_1347_ = lean_unsigned_to_nat(0);
                                    v___x_1348_ = l_Lean_Syntax_getArg(v___x_1343_, v___x_1342_);
                                    v___x_1349_ =
                                        l_Lean_Syntax_matchesNull(v___x_1348_, v___x_1347_);
                                    if v___x_1349_ == 0 {
                                        lean_dec(v___x_1343_);
                                        v___x_1350_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v___x_1350_, 0, v_x_1279_);
                                        return v___x_1350_;
                                    } else {
                                        lean_dec(v_x_1279_);
                                        v___x_1351_ = lean_unsigned_to_nat(3);
                                        v_b_1352_ = l_Lean_Syntax_getArg(v___x_1343_, v___x_1351_);
                                        v___x_1353_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_b_1352_, v___y_1280_);
                                        if lean_obj_tag(v___x_1353_) == 0 {
                                            v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
                                            v_isSharedCheck_1375_ =
                                                (!lean_is_exclusive(v___x_1353_)) as u8;
                                            if v_isSharedCheck_1375_ == 0 {
                                                v___x_1356_ = v___x_1353_;
                                                v_isShared_1357_ = v_isSharedCheck_1375_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1354_);
                                                lean_dec(v___x_1353_);
                                                v___x_1356_ = lean_box(0);
                                                v_isShared_1357_ = v_isSharedCheck_1375_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v___x_1343_);
                                            return v___x_1353_;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_1376_ = lean_unsigned_to_nat(3);
                            v_t_1377_ = l_Lean_Syntax_getArg(v_x_1279_, v___x_1376_);
                            v___x_1378_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_t_1377_, v___y_1280_);
                            if lean_obj_tag(v___x_1378_) == 0 {
                                v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
                                lean_inc(v_a_1379_);
                                lean_dec_ref_known(v___x_1378_, 1);
                                v___x_1380_ = lean_unsigned_to_nat(5);
                                v_e_1381_ = l_Lean_Syntax_getArg(v_x_1279_, v___x_1380_);
                                v___x_1382_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_e_1381_, v___y_1280_);
                                if lean_obj_tag(v___x_1382_) == 0 {
                                    v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
                                    v_isSharedCheck_1401_ = (!lean_is_exclusive(v___x_1382_)) as u8;
                                    if v_isSharedCheck_1401_ == 0 {
                                        v___x_1385_ = v___x_1382_;
                                        v_isShared_1386_ = v_isSharedCheck_1401_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1383_);
                                        lean_dec(v___x_1382_);
                                        v___x_1385_ = lean_box(0);
                                        v_isShared_1386_ = v_isSharedCheck_1401_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1379_);
                                    lean_dec(v_x_1279_);
                                    return v___x_1382_;
                                }
                            } else {
                                lean_dec(v_x_1279_);
                                return v___x_1378_;
                            }
                        }
                    } else {
                        v___x_1402_ = lean_unsigned_to_nat(0);
                        v___x_1403_ = l_Lean_Syntax_getArg(v_x_1279_, v___x_1402_);
                        v___x_1404_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16;
                        lean_inc(v___x_1403_);
                        v___x_1405_ = l_Lean_Syntax_isOfKind(v___x_1403_, v___x_1404_);
                        if v___x_1405_ == 0 {
                            lean_dec(v___x_1403_);
                            v___x_1406_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1406_, 0, v_x_1279_);
                            return v___x_1406_;
                        } else {
                            v___x_1407_ = lean_unsigned_to_nat(1);
                            v___x_1408_ = l_Lean_Syntax_getArg(v___x_1403_, v___x_1407_);
                            lean_dec(v___x_1403_);
                            v___x_1409_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18;
                            lean_inc(v___x_1408_);
                            v___x_1410_ = l_Lean_Syntax_isOfKind(v___x_1408_, v___x_1409_);
                            if v___x_1410_ == 0 {
                                lean_dec(v___x_1408_);
                                v___x_1411_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1411_, 0, v_x_1279_);
                                return v___x_1411_;
                            } else {
                                v___x_1412_ = l_Lean_Syntax_getArg(v___x_1408_, v___x_1402_);
                                lean_dec(v___x_1408_);
                                v___x_1413_ = lean_box(0);
                                v___x_1414_ = l_Lean_Syntax_matchesIdent(v___x_1412_, v___x_1413_);
                                lean_dec(v___x_1412_);
                                if v___x_1414_ == 0 {
                                    v___x_1415_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_1415_, 0, v_x_1279_);
                                    return v___x_1415_;
                                } else {
                                    v_P_1416_ = l_Lean_Syntax_getArg(v_x_1279_, v___x_1407_);
                                    lean_dec(v_x_1279_);
                                    v___x_1417_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_P_1416_, v___y_1280_);
                                    if lean_obj_tag(v___x_1417_) == 0 {
                                        v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
                                        v_isSharedCheck_1440_ =
                                            (!lean_is_exclusive(v___x_1417_)) as u8;
                                        if v_isSharedCheck_1440_ == 0 {
                                            v___x_1420_ = v___x_1417_;
                                            v_isShared_1421_ = v_isSharedCheck_1440_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1418_);
                                            lean_dec(v___x_1417_);
                                            v___x_1420_ = lean_box(0);
                                            v_isShared_1421_ = v_isSharedCheck_1440_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        return v___x_1417_;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    v___x_1441_ = lean_unsigned_to_nat(1);
                    v___x_1442_ = l_Lean_Syntax_getArg(v_x_1279_, v___x_1441_);
                    lean_dec(v_x_1279_);
                    v___x_1443_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1443_, 0, v___x_1442_);
                    return v___x_1443_;
                }
            }
            1 => {
                v_ref_1318_ = lean_ctor_get(v___y_1280_, 5);
                v_quotContext_1319_ = lean_ctor_get(v___y_1280_, 10);
                v_currMacroScope_1320_ = lean_ctor_get(v___y_1280_, 11);
                v___x_1321_ = l_Lean_Syntax_getArg(v___x_1309_, v___x_1294_);
                lean_dec(v___x_1309_);
                v___x_1322_ = l_Lean_SourceInfo_fromRef(v_ref_1318_, v___x_1290_);
                v___x_1323_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19;
                lean_inc_n(v___x_1322_, 7);
                v___x_1324_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1324_, 0, v___x_1322_);
                lean_ctor_set(v___x_1324_, 1, v___x_1323_);
                v___x_1325_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21);
                lean_inc(v_currMacroScope_1320_);
                lean_inc(v_quotContext_1319_);
                v___x_1326_ =
                    l_Lean_addMacroScope(v_quotContext_1319_, v___x_1305_, v_currMacroScope_1320_);
                v___x_1327_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40;
                v___x_1328_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1328_, 0, v___x_1322_);
                lean_ctor_set(v___x_1328_, 1, v___x_1325_);
                lean_ctor_set(v___x_1328_, 2, v___x_1326_);
                lean_ctor_set(v___x_1328_, 3, v___x_1327_);
                v___x_1329_ = l_Lean_Syntax_node1(v___x_1322_, v___x_1301_, v___x_1328_);
                v___x_1330_ =
                    l_Lean_Syntax_node2(v___x_1322_, v___x_1296_, v___x_1324_, v___x_1329_);
                v___x_1331_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41;
                v___x_1332_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1332_, 0, v___x_1322_);
                lean_ctor_set(v___x_1332_, 1, v___x_1331_);
                v___x_1333_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43;
                v___x_1334_ = l_Lean_Syntax_node1(v___x_1322_, v___x_1333_, v___x_1321_);
                v___x_1335_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44;
                v___x_1336_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1336_, 0, v___x_1322_);
                lean_ctor_set(v___x_1336_, 1, v___x_1335_);
                v___x_1337_ = l_Lean_Syntax_node5(
                    v___x_1322_,
                    v___x_1291_,
                    v___x_1330_,
                    v_a_1314_,
                    v___x_1332_,
                    v___x_1334_,
                    v___x_1336_,
                );
                if v_isShared_1317_ == 0 {
                    lean_ctor_set(v___x_1316_, 0, v___x_1337_);
                    v___x_1339_ = v___x_1316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
                    v___x_1339_ = v_reuseFailAlloc_1340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1339_;
            }
            3 => {
                v_ref_1358_ = lean_ctor_get(v___y_1280_, 5);
                v___x_1359_ = l_Lean_Syntax_getArg(v___x_1343_, v___x_1347_);
                lean_dec(v___x_1343_);
                v_xs_1360_ = l_Lean_Syntax_getArgs(v___x_1359_);
                lean_dec(v___x_1359_);
                v___x_1361_ = l_Lean_SourceInfo_fromRef(v_ref_1358_, v___x_1287_);
                lean_inc_n(v___x_1361_, 5);
                v___x_1362_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1362_, 0, v___x_1361_);
                lean_ctor_set(v___x_1362_, 1, v___x_1288_);
                v___x_1363_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43;
                v___x_1364_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47);
                v___x_1365_ = l_Array_append___redArg(v___x_1364_, v_xs_1360_);
                lean_dec_ref(v_xs_1360_);
                v___x_1366_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1366_, 0, v___x_1361_);
                lean_ctor_set(v___x_1366_, 1, v___x_1363_);
                lean_ctor_set(v___x_1366_, 2, v___x_1365_);
                v___x_1367_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1367_, 0, v___x_1361_);
                lean_ctor_set(v___x_1367_, 1, v___x_1363_);
                lean_ctor_set(v___x_1367_, 2, v___x_1364_);
                v___x_1368_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__48;
                v___x_1369_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1369_, 0, v___x_1361_);
                lean_ctor_set(v___x_1369_, 1, v___x_1368_);
                v___x_1370_ = l_Lean_Syntax_node4(
                    v___x_1361_,
                    v___x_1344_,
                    v___x_1366_,
                    v___x_1367_,
                    v___x_1369_,
                    v_a_1354_,
                );
                v___x_1371_ =
                    l_Lean_Syntax_node2(v___x_1361_, v___x_1289_, v___x_1362_, v___x_1370_);
                if v_isShared_1357_ == 0 {
                    lean_ctor_set(v___x_1356_, 0, v___x_1371_);
                    v___x_1373_ = v___x_1356_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
                    v___x_1373_ = v_reuseFailAlloc_1374_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1373_;
            }
            5 => {
                v_ref_1387_ = lean_ctor_get(v___y_1280_, 5);
                v___x_1388_ = lean_unsigned_to_nat(1);
                v___x_1389_ = l_Lean_Syntax_getArg(v_x_1279_, v___x_1388_);
                lean_dec(v_x_1279_);
                v___x_1390_ = l_Lean_SourceInfo_fromRef(v_ref_1387_, v___x_1285_);
                v___x_1391_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__49;
                lean_inc_n(v___x_1390_, 3);
                v___x_1392_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1392_, 0, v___x_1390_);
                lean_ctor_set(v___x_1392_, 1, v___x_1391_);
                v___x_1393_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__50;
                v___x_1394_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1394_, 0, v___x_1390_);
                lean_ctor_set(v___x_1394_, 1, v___x_1393_);
                v___x_1395_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__51;
                v___x_1396_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1396_, 0, v___x_1390_);
                lean_ctor_set(v___x_1396_, 1, v___x_1395_);
                v___x_1397_ = l_Lean_Syntax_node6(
                    v___x_1390_,
                    v___x_1286_,
                    v___x_1392_,
                    v___x_1389_,
                    v___x_1394_,
                    v_a_1379_,
                    v___x_1396_,
                    v_a_1383_,
                );
                if v_isShared_1386_ == 0 {
                    lean_ctor_set(v___x_1385_, 0, v___x_1397_);
                    v___x_1399_ = v___x_1385_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
                    v___x_1399_ = v_reuseFailAlloc_1400_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1399_;
            }
            7 => {
                v_ref_1422_ = lean_ctor_get(v___y_1280_, 5);
                v_quotContext_1423_ = lean_ctor_get(v___y_1280_, 10);
                v_currMacroScope_1424_ = lean_ctor_get(v___y_1280_, 11);
                v___x_1425_ = l_Lean_SourceInfo_fromRef(v_ref_1422_, v___x_1283_);
                v___x_1426_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19;
                lean_inc_n(v___x_1425_, 5);
                v___x_1427_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1427_, 0, v___x_1425_);
                lean_ctor_set(v___x_1427_, 1, v___x_1426_);
                v___x_1428_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21);
                lean_inc(v_currMacroScope_1424_);
                lean_inc(v_quotContext_1423_);
                v___x_1429_ =
                    l_Lean_addMacroScope(v_quotContext_1423_, v___x_1413_, v_currMacroScope_1424_);
                v___x_1430_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40;
                v___x_1431_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1431_, 0, v___x_1425_);
                lean_ctor_set(v___x_1431_, 1, v___x_1428_);
                lean_ctor_set(v___x_1431_, 2, v___x_1429_);
                lean_ctor_set(v___x_1431_, 3, v___x_1430_);
                v___x_1432_ = l_Lean_Syntax_node1(v___x_1425_, v___x_1409_, v___x_1431_);
                v___x_1433_ =
                    l_Lean_Syntax_node2(v___x_1425_, v___x_1404_, v___x_1427_, v___x_1432_);
                v___x_1434_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44;
                v___x_1435_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1435_, 0, v___x_1425_);
                lean_ctor_set(v___x_1435_, 1, v___x_1434_);
                v___x_1436_ = l_Lean_Syntax_node3(
                    v___x_1425_,
                    v___x_1284_,
                    v___x_1433_,
                    v_a_1418_,
                    v___x_1435_,
                );
                if v_isShared_1421_ == 0 {
                    lean_ctor_set(v___x_1420_, 0, v___x_1436_);
                    v___x_1438_ = v___x_1420_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
                    v___x_1438_ = v_reuseFailAlloc_1439_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___boxed(
    mut v_x_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
    mut v___y_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1447_: *mut LeanObject = core::ptr::null_mut();
    v_res_1447_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_x_1444_, v___y_1445_);
    lean_dec_ref(v___y_1445_);
    return v_res_1447_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(
    mut v_x_1448_: *mut LeanObject,
    mut v___y_1449_: *mut LeanObject,
    mut v___y_1450_: *mut LeanObject,
    mut v___y_1451_: *mut LeanObject,
    mut v___y_1452_: *mut LeanObject,
    mut v___y_1453_: *mut LeanObject,
    mut v___y_1454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    v___x_1456_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_1449_);
    v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
    lean_inc(v_a_1457_);
    lean_dec_ref(v___x_1456_);
    v___x_1458_ = l_Lean_Expr_appFn_x21(v_a_1457_);
    lean_dec(v_a_1457_);
    v___x_1459_ = lean_unsigned_to_nat(0);
    v___x_1460_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v___x_1458_, v___x_1459_, v_x_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
    return v___x_1460_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg___boxed(
    mut v_x_1461_: *mut LeanObject,
    mut v___y_1462_: *mut LeanObject,
    mut v___y_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
    mut v___y_1465_: *mut LeanObject,
    mut v___y_1466_: *mut LeanObject,
    mut v___y_1467_: *mut LeanObject,
    mut v___y_1468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1469_: *mut LeanObject = core::ptr::null_mut();
    v_res_1469_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v_x_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
    lean_dec(v___y_1467_);
    lean_dec_ref(v___y_1466_);
    lean_dec(v___y_1465_);
    lean_dec_ref(v___y_1464_);
    lean_dec(v___y_1463_);
    lean_dec_ref(v___y_1462_);
    return v_res_1469_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(
    mut v_t_1470_: *mut LeanObject,
    mut v_k_1471_: *mut LeanObject,
    mut v_fallback_1472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1470_) == 0 {
                    v_k_1473_ = lean_ctor_get(v_t_1470_, 1);
                    v_v_1474_ = lean_ctor_get(v_t_1470_, 2);
                    v_l_1475_ = lean_ctor_get(v_t_1470_, 3);
                    v_r_1476_ = lean_ctor_get(v_t_1470_, 4);
                    v___x_1477_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1471_, v_k_1473_);
                    match v___x_1477_ {
                        0 => {
                            v_t_1470_ = v_l_1475_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_1474_);
                            return v_v_1474_;
                        }
                        _ => {
                            v_t_1470_ = v_r_1476_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_fallback_1472_);
                    return v_fallback_1472_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg___boxed(
    mut v_t_1480_: *mut LeanObject,
    mut v_k_1481_: *mut LeanObject,
    mut v_fallback_1482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1483_: *mut LeanObject = core::ptr::null_mut();
    v_res_1483_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(v_t_1480_, v_k_1481_, v_fallback_1482_);
    lean_dec(v_fallback_1482_);
    lean_dec(v_k_1481_);
    lean_dec(v_t_1480_);
    return v_res_1483_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed(
    mut v_acc_1493_: *mut LeanObject,
    mut v_a_1494_: *mut LeanObject,
    mut v_a_1495_: *mut LeanObject,
    mut v_a_1496_: *mut LeanObject,
    mut v_a_1497_: *mut LeanObject,
    mut v_a_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1501_: *mut LeanObject = core::ptr::null_mut();
    v_res_1501_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses(v_acc_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
    lean_dec(v_a_1499_);
    lean_dec_ref(v_a_1498_);
    lean_dec(v_a_1497_);
    lean_dec_ref(v_a_1496_);
    lean_dec(v_a_1495_);
    lean_dec_ref(v_a_1494_);
    return v_res_1501_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses(
    mut v_acc_1502_: *mut LeanObject,
    mut v_a_1503_: *mut LeanObject,
    mut v_a_1504_: *mut LeanObject,
    mut v_a_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
    mut v_a_1507_: *mut LeanObject,
    mut v_a_1508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1525_: u8 = 0;
    let mut v_fst_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v___y_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_accessibles_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inaccessibles_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: u8 = 0;
    let mut v_fst_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut v_a_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut v___y_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: u8 = 0;
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v_isSharedCheck_1602_: u8 = 0;
    let mut v_unused_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_a_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1616_: u8 = 0;
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1510_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v_a_1503_);
                if lean_obj_tag(v___x_1510_) == 0 {
                    v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
                    v_isSharedCheck_1612_ = (!lean_is_exclusive(v___x_1510_)) as u8;
                    if v_isSharedCheck_1612_ == 0 {
                        v___x_1513_ = v___x_1510_;
                        v_isShared_1514_ = v_isSharedCheck_1612_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1511_);
                        lean_dec(v___x_1510_);
                        v___x_1513_ = lean_box(0);
                        v_isShared_1514_ = v_isSharedCheck_1612_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_acc_1502_);
                    v_a_1613_ = lean_ctor_get(v___x_1510_, 0);
                    v_isSharedCheck_1620_ = (!lean_is_exclusive(v___x_1510_)) as u8;
                    if v_isSharedCheck_1620_ == 0 {
                        v___x_1615_ = v___x_1510_;
                        v_isShared_1616_ = v_isSharedCheck_1620_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_1613_);
                        lean_dec(v___x_1510_);
                        v___x_1615_ = lean_box(0);
                        v_isShared_1616_ = v_isSharedCheck_1620_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_1511_);
                v___x_1515_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_a_1511_);
                if lean_obj_tag(v___x_1515_) == 1 {
                    lean_dec_ref_known(v___x_1515_, 1);
                    lean_dec(v_a_1511_);
                    if v_isShared_1514_ == 0 {
                        lean_ctor_set(v___x_1513_, 0, v_acc_1502_);
                        v___x_1517_ = v___x_1513_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_acc_1502_);
                        v___x_1517_ = v_reuseFailAlloc_1518_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1515_);
                    lean_inc(v_a_1511_);
                    v___x_1519_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_a_1511_);
                    if lean_obj_tag(v___x_1519_) == 1 {
                        lean_dec(v_a_1511_);
                        v_snd_1520_ = lean_ctor_get(v_acc_1502_, 1);
                        lean_inc(v_snd_1520_);
                        v_val_1521_ = lean_ctor_get(v___x_1519_, 0);
                        lean_inc(v_val_1521_);
                        lean_dec_ref_known(v___x_1519_, 1);
                        v_fst_1522_ = lean_ctor_get(v_acc_1502_, 0);
                        v_isSharedCheck_1602_ = (!lean_is_exclusive(v_acc_1502_)) as u8;
                        if v_isSharedCheck_1602_ == 0 {
                            v_unused_1603_ = lean_ctor_get(v_acc_1502_, 1);
                            lean_dec(v_unused_1603_);
                            v___x_1524_ = v_acc_1502_;
                            v_isShared_1525_ = v_isSharedCheck_1602_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_fst_1522_);
                            lean_dec(v_acc_1502_);
                            v___x_1524_ = lean_box(0);
                            v_isShared_1525_ = v_isSharedCheck_1602_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1519_);
                        lean_del_object(v___x_1513_);
                        v___x_1604_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_a_1511_);
                        lean_dec(v_a_1511_);
                        if lean_obj_tag(v___x_1604_) == 0 {
                            lean_dec_ref(v_acc_1502_);
                            v___x_1605_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
                            return v___x_1605_;
                        } else {
                            lean_dec_ref_known(v___x_1604_, 1);
                            v___x_1606_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed as *mut core::ffi::c_void, 8, 1);
                            lean_closure_set(v___x_1606_, 0, v_acc_1502_);
                            v___x_1607_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v___x_1606_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
                            if lean_obj_tag(v___x_1607_) == 0 {
                                v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
                                lean_inc(v_a_1608_);
                                lean_dec_ref_known(v___x_1607_, 1);
                                v___x_1609_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed as *mut core::ffi::c_void, 8, 1);
                                lean_closure_set(v___x_1609_, 0, v_a_1608_);
                                v___x_1610_ = lean_alloc_closure(l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___boxed as *mut core::ffi::c_void, 9, 2);
                                lean_closure_set(v___x_1610_, 0, lean_box(0));
                                lean_closure_set(v___x_1610_, 1, v___x_1609_);
                                v___x_1611_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v___x_1610_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
                                return v___x_1611_;
                            } else {
                                return v___x_1607_;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1517_;
            }
            3 => {
                v_fst_1526_ = lean_ctor_get(v_snd_1520_, 0);
                v_snd_1527_ = lean_ctor_get(v_snd_1520_, 1);
                v_isSharedCheck_1601_ = (!lean_is_exclusive(v_snd_1520_)) as u8;
                if v_isSharedCheck_1601_ == 0 {
                    v___x_1529_ = v_snd_1520_;
                    v_isShared_1530_ = v_isSharedCheck_1601_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_1527_);
                    lean_inc(v_fst_1526_);
                    lean_dec(v_snd_1520_);
                    v___x_1529_ = lean_box(0);
                    v_isShared_1530_ = v_isSharedCheck_1601_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_name_1545_ = lean_ctor_get(v_val_1521_, 0);
                lean_inc_n(v_name_1545_, 2);
                lean_dec(v_val_1521_);
                v___x_1546_ = lean_erase_macro_scopes(v_name_1545_);
                v___x_1547_ = l_Lean_Name_hasMacroScopes(v_name_1545_);
                lean_dec(v_name_1545_);
                if v___x_1547_ == 0 {
                    v___x_1596_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_fst_1522_, v___x_1546_);
                    if lean_obj_tag(v___x_1596_) == 1 {
                        v_val_1597_ = lean_ctor_get(v___x_1596_, 0);
                        lean_inc(v_val_1597_);
                        lean_dec_ref_known(v___x_1596_, 1);
                        v_val_1587_ = v_val_1597_;
                        state = 15;
                        continue;
                    } else {
                        lean_dec(v___x_1596_);
                        v___x_1598_ = lean_unsigned_to_nat(0);
                        lean_inc(v___x_1546_);
                        v_fst_1549_ = v___x_1598_;
                        v_snd_1550_ = v___x_1546_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___x_1599_ = lean_unsigned_to_nat(0);
                    v___x_1600_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(v_fst_1526_, v___x_1546_, v___x_1599_);
                    v_val_1587_ = v___x_1600_;
                    state = 15;
                    continue;
                }
            }
            5 => {
                v___x_1535_ = lean_array_push(v_snd_1527_, v___y_1532_);
                if v_isShared_1530_ == 0 {
                    lean_ctor_set(v___x_1529_, 1, v___x_1535_);
                    lean_ctor_set(v___x_1529_, 0, v_inaccessibles_1534_);
                    v___x_1537_ = v___x_1529_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_inaccessibles_1534_);
                    lean_ctor_set(v_reuseFailAlloc_1544_, 1, v___x_1535_);
                    v___x_1537_ = v_reuseFailAlloc_1544_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1525_ == 0 {
                    lean_ctor_set(v___x_1524_, 1, v___x_1537_);
                    lean_ctor_set(v___x_1524_, 0, v_accessibles_1533_);
                    v___x_1539_ = v___x_1524_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_accessibles_1533_);
                    lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1537_);
                    v___x_1539_ = v_reuseFailAlloc_1543_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1514_ == 0 {
                    lean_ctor_set(v___x_1513_, 0, v___x_1539_);
                    v___x_1541_ = v___x_1513_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
                    v___x_1541_ = v_reuseFailAlloc_1542_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1541_;
            }
            9 => {
                v___x_1551_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0;
                v___x_1552_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(v___x_1551_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
                if lean_obj_tag(v___x_1552_) == 0 {
                    v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
                    lean_inc(v_a_1553_);
                    lean_dec_ref_known(v___x_1552_, 1);
                    v___x_1554_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_a_1553_, v_a_1507_);
                    if lean_obj_tag(v___x_1554_) == 0 {
                        v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
                        lean_inc(v_a_1555_);
                        lean_dec_ref_known(v___x_1554_, 1);
                        v_ref_1556_ = lean_ctor_get(v_a_1507_, 5);
                        v___x_1557_ = lean_mk_syntax_ident(v_snd_1550_);
                        v___x_1558_ = 0;
                        v___x_1559_ = l_Lean_SourceInfo_fromRef(v_ref_1556_, v___x_1558_);
                        v___x_1560_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3;
                        v___x_1561_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41;
                        lean_inc(v___x_1559_);
                        v___x_1562_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_1562_, 0, v___x_1559_);
                        lean_ctor_set(v___x_1562_, 1, v___x_1561_);
                        v___x_1563_ = l_Lean_Syntax_node3(
                            v___x_1559_,
                            v___x_1560_,
                            v___x_1557_,
                            v___x_1562_,
                            v_a_1555_,
                        );
                        if v___x_1547_ == 0 {
                            v___x_1564_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1546_, v_fst_1549_, v_fst_1522_);
                            v___y_1532_ = v___x_1563_;
                            v_accessibles_1533_ = v___x_1564_;
                            v_inaccessibles_1534_ = v_fst_1526_;
                            state = 5;
                            continue;
                        } else {
                            v___x_1565_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1546_, v_fst_1549_, v_fst_1526_);
                            v___y_1532_ = v___x_1563_;
                            v_accessibles_1533_ = v_fst_1522_;
                            v_inaccessibles_1534_ = v___x_1565_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_1550_);
                        lean_dec(v_fst_1549_);
                        lean_dec(v___x_1546_);
                        lean_del_object(v___x_1529_);
                        lean_dec(v_snd_1527_);
                        lean_dec(v_fst_1526_);
                        lean_del_object(v___x_1524_);
                        lean_dec(v_fst_1522_);
                        lean_del_object(v___x_1513_);
                        v_a_1566_ = lean_ctor_get(v___x_1554_, 0);
                        v_isSharedCheck_1573_ = (!lean_is_exclusive(v___x_1554_)) as u8;
                        if v_isSharedCheck_1573_ == 0 {
                            v___x_1568_ = v___x_1554_;
                            v_isShared_1569_ = v_isSharedCheck_1573_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1566_);
                            lean_dec(v___x_1554_);
                            v___x_1568_ = lean_box(0);
                            v_isShared_1569_ = v_isSharedCheck_1573_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_1550_);
                    lean_dec(v_fst_1549_);
                    lean_dec(v___x_1546_);
                    lean_del_object(v___x_1529_);
                    lean_dec(v_snd_1527_);
                    lean_dec(v_fst_1526_);
                    lean_del_object(v___x_1524_);
                    lean_dec(v_fst_1522_);
                    lean_del_object(v___x_1513_);
                    v_a_1574_ = lean_ctor_get(v___x_1552_, 0);
                    v_isSharedCheck_1581_ = (!lean_is_exclusive(v___x_1552_)) as u8;
                    if v_isSharedCheck_1581_ == 0 {
                        v___x_1576_ = v___x_1552_;
                        v_isShared_1577_ = v_isSharedCheck_1581_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1574_);
                        lean_dec(v___x_1552_);
                        v___x_1576_ = lean_box(0);
                        v_isShared_1577_ = v_isSharedCheck_1581_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_1569_ == 0 {
                    v___x_1571_ = v___x_1568_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
                    v___x_1571_ = v_reuseFailAlloc_1572_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1571_;
            }
            12 => {
                if v_isShared_1577_ == 0 {
                    v___x_1579_ = v___x_1576_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
                    v___x_1579_ = v_reuseFailAlloc_1580_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1579_;
            }
            14 => {
                lean_inc(v___x_1546_);
                v___x_1585_ = lean_name_append_after(v___x_1546_, v___y_1584_);
                v_fst_1549_ = v___y_1583_;
                v_snd_1550_ = v___x_1585_;
                state = 9;
                continue;
            }
            15 => {
                v___x_1588_ = lean_unsigned_to_nat(1);
                v___x_1589_ = lean_nat_add(v_val_1587_, v___x_1588_);
                v___x_1590_ = lean_unsigned_to_nat(0);
                v___x_1591_ = lean_nat_dec_eq(v_val_1587_, v___x_1590_);
                if v___x_1591_ == 0 {
                    v___x_1592_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4;
                    v___x_1593_ = l_Nat_toSuperscriptString(v_val_1587_);
                    v___x_1594_ = lean_string_append(v___x_1592_, v___x_1593_);
                    lean_dec_ref(v___x_1593_);
                    v___y_1583_ = v___x_1589_;
                    v___y_1584_ = v___x_1594_;
                    state = 14;
                    continue;
                } else {
                    lean_dec(v_val_1587_);
                    v___x_1595_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4;
                    v___y_1583_ = v___x_1589_;
                    v___y_1584_ = v___x_1595_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                if v_isShared_1616_ == 0 {
                    v___x_1618_ = v___x_1615_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
                    v___x_1618_ = v_reuseFailAlloc_1619_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2(
    mut v_x_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
    mut v___y_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_x_1621_, v___y_1626_);
    return v___x_1629_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___boxed(
    mut v_x_1630_: *mut LeanObject,
    mut v___y_1631_: *mut LeanObject,
    mut v___y_1632_: *mut LeanObject,
    mut v___y_1633_: *mut LeanObject,
    mut v___y_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
    mut v___y_1637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1638_: *mut LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2(v_x_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
    lean_dec(v___y_1636_);
    lean_dec_ref(v___y_1635_);
    lean_dec(v___y_1634_);
    lean_dec_ref(v___y_1633_);
    lean_dec(v___y_1632_);
    lean_dec_ref(v___y_1631_);
    return v_res_1638_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3(
    mut v_00_u03b4_1639_: *mut LeanObject,
    mut v_t_1640_: *mut LeanObject,
    mut v_k_1641_: *mut LeanObject,
    mut v_fallback_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    v___x_1643_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(v_t_1640_, v_k_1641_, v_fallback_1642_);
    return v___x_1643_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___boxed(
    mut v_00_u03b4_1644_: *mut LeanObject,
    mut v_t_1645_: *mut LeanObject,
    mut v_k_1646_: *mut LeanObject,
    mut v_fallback_1647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1648_: *mut LeanObject = core::ptr::null_mut();
    v_res_1648_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3(v_00_u03b4_1644_, v_t_1645_, v_k_1646_, v_fallback_1647_);
    lean_dec(v_fallback_1647_);
    lean_dec(v_k_1646_);
    lean_dec(v_t_1645_);
    return v_res_1648_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5(
    mut v_00_u03b1_1649_: *mut LeanObject,
    mut v_child_1650_: *mut LeanObject,
    mut v_childIdx_1651_: *mut LeanObject,
    mut v_x_1652_: *mut LeanObject,
    mut v___y_1653_: *mut LeanObject,
    mut v___y_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    v___x_1660_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v_child_1650_, v_childIdx_1651_, v_x_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
    return v___x_1660_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___boxed(
    mut v_00_u03b1_1661_: *mut LeanObject,
    mut v_child_1662_: *mut LeanObject,
    mut v_childIdx_1663_: *mut LeanObject,
    mut v_x_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1672_: *mut LeanObject = core::ptr::null_mut();
    v_res_1672_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5(v_00_u03b1_1661_, v_child_1662_, v_childIdx_1663_, v_x_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
    lean_dec(v___y_1670_);
    lean_dec_ref(v___y_1669_);
    lean_dec(v___y_1668_);
    lean_dec_ref(v___y_1667_);
    lean_dec(v___y_1666_);
    lean_dec_ref(v___y_1665_);
    return v_res_1672_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5(
    mut v_00_u03b1_1673_: *mut LeanObject,
    mut v_x_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    v___x_1682_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v_x_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
    return v___x_1682_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___boxed(
    mut v_00_u03b1_1683_: *mut LeanObject,
    mut v_x_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1692_: *mut LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5(v_00_u03b1_1683_, v_x_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
    lean_dec(v___y_1690_);
    lean_dec_ref(v___y_1689_);
    lean_dec(v___y_1688_);
    lean_dec_ref(v___y_1687_);
    lean_dec(v___y_1686_);
    lean_dec_ref(v___y_1685_);
    return v_res_1692_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal(
    mut v_a_1712_: *mut LeanObject,
    mut v_a_1713_: *mut LeanObject,
    mut v_a_1714_: *mut LeanObject,
    mut v_a_1715_: *mut LeanObject,
    mut v_a_1716_: *mut LeanObject,
    mut v_a_1717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1735_: u8 = 0;
    let mut v_ref_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: u8 = 0;
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1753_: u8 = 0;
    let mut v_isSharedCheck_1754_: u8 = 0;
    let mut v_unused_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1773_: u8 = 0;
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1764_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v_a_1712_);
                v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
                lean_inc(v_a_1765_);
                lean_dec_ref(v___x_1764_);
                v___x_1766_ = lean_unsigned_to_nat(3);
                v___x_1767_ = l_Lean_Expr_getAppNumArgs(v_a_1765_);
                lean_dec(v_a_1765_);
                v___x_1768_ = lean_nat_dec_le(v___x_1766_, v___x_1767_);
                lean_dec(v___x_1767_);
                if v___x_1768_ == 0 {
                    v___x_1769_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
                    if lean_obj_tag(v___x_1769_) == 0 {
                        lean_dec_ref_known(v___x_1769_, 1);
                        state = 1;
                        continue;
                    } else {
                        v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
                        v_isSharedCheck_1777_ = (!lean_is_exclusive(v___x_1769_)) as u8;
                        if v_isSharedCheck_1777_ == 0 {
                            v___x_1772_ = v___x_1769_;
                            v_isShared_1773_ = v_isSharedCheck_1777_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1770_);
                            lean_dec(v___x_1769_);
                            v___x_1772_ = lean_box(0);
                            v_isShared_1773_ = v_isSharedCheck_1777_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1720_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__4;
                v___x_1721_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v___x_1720_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
                if lean_obj_tag(v___x_1721_) == 0 {
                    v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
                    lean_inc(v_a_1722_);
                    lean_dec_ref_known(v___x_1721_, 1);
                    v_snd_1723_ = lean_ctor_get(v_a_1722_, 1);
                    lean_inc(v_snd_1723_);
                    lean_dec(v_a_1722_);
                    v_snd_1724_ = lean_ctor_get(v_snd_1723_, 1);
                    v_isSharedCheck_1754_ = (!lean_is_exclusive(v_snd_1723_)) as u8;
                    if v_isSharedCheck_1754_ == 0 {
                        v_unused_1755_ = lean_ctor_get(v_snd_1723_, 0);
                        lean_dec(v_unused_1755_);
                        v___x_1726_ = v_snd_1723_;
                        v_isShared_1727_ = v_isSharedCheck_1754_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_1724_);
                        lean_dec(v_snd_1723_);
                        v___x_1726_ = lean_box(0);
                        v_isShared_1727_ = v_isSharedCheck_1754_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1756_ = lean_ctor_get(v___x_1721_, 0);
                    v_isSharedCheck_1763_ = (!lean_is_exclusive(v___x_1721_)) as u8;
                    if v_isSharedCheck_1763_ == 0 {
                        v___x_1758_ = v___x_1721_;
                        v_isShared_1759_ = v_isSharedCheck_1763_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1756_);
                        lean_dec(v___x_1721_);
                        v___x_1758_ = lean_box(0);
                        v_isShared_1759_ = v_isSharedCheck_1763_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1728_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0;
                v___x_1729_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v___x_1728_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
                if lean_obj_tag(v___x_1729_) == 0 {
                    v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
                    lean_inc(v_a_1730_);
                    lean_dec_ref_known(v___x_1729_, 1);
                    v___x_1731_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_a_1730_, v_a_1716_);
                    if lean_obj_tag(v___x_1731_) == 0 {
                        v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
                        v_isSharedCheck_1753_ = (!lean_is_exclusive(v___x_1731_)) as u8;
                        if v_isSharedCheck_1753_ == 0 {
                            v___x_1734_ = v___x_1731_;
                            v_isShared_1735_ = v_isSharedCheck_1753_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1732_);
                            lean_dec(v___x_1731_);
                            v___x_1734_ = lean_box(0);
                            v_isShared_1735_ = v_isSharedCheck_1753_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1726_);
                        lean_dec(v_snd_1724_);
                        return v___x_1731_;
                    }
                } else {
                    lean_del_object(v___x_1726_);
                    lean_dec(v_snd_1724_);
                    return v___x_1729_;
                }
            }
            3 => {
                v_ref_1736_ = lean_ctor_get(v_a_1716_, 5);
                v___x_1737_ = 0;
                v___x_1738_ = l_Lean_SourceInfo_fromRef(v_ref_1736_, v___x_1737_);
                v___x_1739_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6;
                v___x_1740_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43;
                v___x_1741_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47);
                v___x_1742_ = l_Array_reverse___redArg(v_snd_1724_);
                v___x_1743_ = l_Array_append___redArg(v___x_1741_, v___x_1742_);
                lean_dec_ref(v___x_1742_);
                lean_inc_n(v___x_1738_, 2);
                v___x_1744_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1744_, 0, v___x_1738_);
                lean_ctor_set(v___x_1744_, 1, v___x_1740_);
                lean_ctor_set(v___x_1744_, 2, v___x_1743_);
                v___x_1745_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__7;
                if v_isShared_1727_ == 0 {
                    lean_ctor_set_tag(v___x_1726_, 2);
                    lean_ctor_set(v___x_1726_, 1, v___x_1745_);
                    lean_ctor_set(v___x_1726_, 0, v___x_1738_);
                    v___x_1747_ = v___x_1726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1752_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1738_);
                    lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1745_);
                    v___x_1747_ = v_reuseFailAlloc_1752_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1748_ = l_Lean_Syntax_node3(
                    v___x_1738_,
                    v___x_1739_,
                    v___x_1744_,
                    v___x_1747_,
                    v_a_1732_,
                );
                if v_isShared_1735_ == 0 {
                    lean_ctor_set(v___x_1734_, 0, v___x_1748_);
                    v___x_1750_ = v___x_1734_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
                    v___x_1750_ = v_reuseFailAlloc_1751_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1750_;
            }
            6 => {
                if v_isShared_1759_ == 0 {
                    v___x_1761_ = v___x_1758_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
                    v___x_1761_ = v_reuseFailAlloc_1762_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1761_;
            }
            8 => {
                if v_isShared_1773_ == 0 {
                    v___x_1775_ = v___x_1772_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
                    v___x_1775_ = v_reuseFailAlloc_1776_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___boxed(
    mut v_a_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
    mut v_a_1780_: *mut LeanObject,
    mut v_a_1781_: *mut LeanObject,
    mut v_a_1782_: *mut LeanObject,
    mut v_a_1783_: *mut LeanObject,
    mut v_a_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1785_: *mut LeanObject = core::ptr::null_mut();
    v_res_1785_ =
        l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal(
            v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_,
        );
    lean_dec(v_a_1783_);
    lean_dec_ref(v_a_1782_);
    lean_dec(v_a_1781_);
    lean_dec_ref(v_a_1780_);
    lean_dec(v_a_1779_);
    lean_dec_ref(v_a_1778_);
    return v_res_1785_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1()
-> *mut LeanObject {
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    v___x_1842_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
    v___x_1843_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2;
    v___x_1844_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__21;
    v___x_1845_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___boxed as *mut core::ffi::c_void, 7, 0);
    v___x_1846_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1842_,
        v___x_1843_,
        v___x_1844_,
        v___x_1845_,
    );
    return v___x_1846_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___boxed(
    mut v_a_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1848_: *mut LeanObject = core::ptr::null_mut();
    v_res_1848_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1();
    return v_res_1848_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker(
    mut v_a_1849_: *mut LeanObject,
    mut v_a_1850_: *mut LeanObject,
    mut v_a_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    v___x_1856_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0;
    v___x_1857_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v___x_1856_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
    if lean_obj_tag(v___x_1857_) == 0 {
        let mut v_a_1858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
        v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
        lean_inc(v_a_1858_);
        lean_dec_ref_known(v___x_1857_, 1);
        v___x_1859_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_a_1858_, v_a_1853_);
        return v___x_1859_;
    } else {
        return v___x_1857_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___boxed(
    mut v_a_1860_: *mut LeanObject,
    mut v_a_1861_: *mut LeanObject,
    mut v_a_1862_: *mut LeanObject,
    mut v_a_1863_: *mut LeanObject,
    mut v_a_1864_: *mut LeanObject,
    mut v_a_1865_: *mut LeanObject,
    mut v_a_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1867_: *mut LeanObject = core::ptr::null_mut();
    v_res_1867_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker(v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
    lean_dec(v_a_1865_);
    lean_dec_ref(v_a_1864_);
    lean_dec(v_a_1863_);
    lean_dec_ref(v_a_1862_);
    lean_dec(v_a_1861_);
    lean_dec_ref(v_a_1860_);
    return v_res_1867_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1()
-> *mut LeanObject {
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    v___x_1880_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
    v___x_1881_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1;
    v___x_1882_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__3;
    v___x_1883_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___boxed as *mut core::ffi::c_void, 7, 0);
    v___x_1884_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1880_,
        v___x_1881_,
        v___x_1882_,
        v___x_1883_,
    );
    return v___x_1884_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___boxed(
    mut v_a_1885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1886_: *mut LeanObject = core::ptr::null_mut();
    v_res_1886_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1();
    return v_res_1886_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin);
}

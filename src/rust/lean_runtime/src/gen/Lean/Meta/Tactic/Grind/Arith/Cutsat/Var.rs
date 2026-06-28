// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt Lean.Meta.IntInstTesters
use crate::r#gen::Init::Data::List::Basic::l_List_elem___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqNat___boxed,
};
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_PersistentArray_push___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::IntInstTesters::{
    initialize_Lean_Meta_IntInstTesters, l_Lean_Meta_Structural_isInstHAddInt___redArg,
    l_Lean_Meta_Structural_isInstHDivInt___redArg, l_Lean_Meta_Structural_isInstHModInt___redArg,
    l_Lean_Meta_Structural_isInstHMulInt___redArg, l_Lean_Meta_Structural_isInstHPowInt___redArg,
    runtime_initialize_Lean_Meta_IntInstTesters,
};
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Nat::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat,
    l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast, l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg,
    l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::ToInt::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt,
    l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types, l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    l_Int_Linear_Poly_isZero, l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_markTerm___redArg, l_Lean_Meta_Grind_getGeneration___redArg,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::lean_grind_cutsat_mk_var;
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_internalize;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__0_value) as *mut LeanObject,12847922472053947547 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__1_value) as *mut LeanObject,10422657989269798688 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__3_value) as *mut LeanObject,13744984671752750173 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__4_value) as *mut LeanObject,9682224670061807480 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__6_value) as *mut LeanObject,11858238400308895562 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__7_value) as *mut LeanObject,6100819061652633370 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__9_value) as *mut LeanObject,2929883540436775422 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__10_value) as *mut LeanObject,1611444129324655608 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0_value: LeanStringObject<6> =
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
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1_value: LeanStringObject<6> =
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
        m_data: [100, 101, 98, 117, 103, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [108, 105, 97, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3_value: LeanStringObject<12> =
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
        m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1_value)
                as *mut LeanObject,
            5637236024813792860 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2_value)
                as *mut LeanObject,
            12441483040187581015 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3_value)
                as *mut LeanObject,
            1477802454752751138 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5_value: LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 4,
        m_data: [32, 226, 134, 166, 32, 35, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [73, 110, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0_value: LeanStringObject<
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
    m_data: [72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1_value: LeanStringObject<
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
    m_data: [104, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0_value)
            as *mut LeanObject,
        10393083817453678557 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1_value)
                as *mut LeanObject,
            10680564408669940870 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3_value: LeanStringObject<
    38,
> = LeanStringObject {
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
        102, 111, 117, 110, 100, 32, 116, 101, 114, 109, 32, 119, 105, 116, 104, 32, 110, 111, 110,
        45, 115, 116, 97, 110, 100, 97, 114, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1_value: LeanStringObject<33> =
    LeanStringObject {
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
            109, 111, 110, 111, 109, 105, 97, 108, 32, 101, 120, 112, 101, 99, 116, 101, 100, 44,
            32, 102, 111, 117, 110, 100, 32, 110, 117, 109, 101, 114, 97, 108, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            10, 105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 105, 110, 103, 32, 97, 115, 32,
            118, 97, 114, 105, 97, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateNonlinearTerm___boxed(
    mut v_y_2237_: *mut LeanObject,
    mut v_x_2238_: *mut LeanObject,
    mut v_a_2239_: *mut LeanObject,
    mut v_a_2240_: *mut LeanObject,
    mut v_a_2241_: *mut LeanObject,
    mut v_a_2242_: *mut LeanObject,
    mut v_a_2243_: *mut LeanObject,
    mut v_a_2244_: *mut LeanObject,
    mut v_a_2245_: *mut LeanObject,
    mut v_a_2246_: *mut LeanObject,
    mut v_a_2247_: *mut LeanObject,
    mut v_a_2248_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2250_: *mut LeanObject = core::ptr::null_mut();
    v_res_2250_ = lean_cutsat_propagate_nonlinear(
        v_y_2237_, v_x_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_,
        v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_,
    );
    return v_res_2250_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(
    mut v_e_2271_: *mut LeanObject,
    mut v_a_2272_: *mut LeanObject,
    mut v_a_2273_: *mut LeanObject,
    mut v_a_2274_: *mut LeanObject,
    mut v_a_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2281_: u8 = 0;
    let mut v___x_2283_: u8 = 0;
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: u8 = 0;
    let mut v_arg_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v_arg_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v_arg_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: u8 = 0;
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u8 = 0;
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u8 = 0;
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: u8 = 0;
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: u8 = 0;
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut v_a_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2336_: u8 = 0;
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2342_: u8 = 0;
    let mut v_a_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2346_: u8 = 0;
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2350_: u8 = 0;
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: u8 = 0;
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2359_: u8 = 0;
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2364_: u8 = 0;
    let mut v_unused_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u8 = 0;
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v_a_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2382_: u8 = 0;
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2386_: u8 = 0;
    let mut v_a_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_a_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2277_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2271_, v_a_2273_);
                if lean_obj_tag(v___x_2277_) == 0 {
                    v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
                    v_isSharedCheck_2395_ = (!lean_is_exclusive(v___x_2277_)) as u8;
                    if v_isSharedCheck_2395_ == 0 {
                        v___x_2280_ = v___x_2277_;
                        v_isShared_2281_ = v_isSharedCheck_2395_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2278_);
                        lean_dec(v___x_2277_);
                        v___x_2280_ = lean_box(0);
                        v_isShared_2281_ = v_isSharedCheck_2395_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2396_ = lean_ctor_get(v___x_2277_, 0);
                    v_isSharedCheck_2403_ = (!lean_is_exclusive(v___x_2277_)) as u8;
                    if v_isSharedCheck_2403_ == 0 {
                        v___x_2398_ = v___x_2277_;
                        v_isShared_2399_ = v_isSharedCheck_2403_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_2396_);
                        lean_dec(v___x_2277_);
                        v___x_2398_ = lean_box(0);
                        v_isShared_2399_ = v_isSharedCheck_2403_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2288_ = l_Lean_Expr_cleanupAnnotations(v_a_2278_);
                v___x_2289_ = l_Lean_Expr_isApp(v___x_2288_);
                if v___x_2289_ == 0 {
                    lean_dec_ref(v___x_2288_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2290_ = lean_ctor_get(v___x_2288_, 1);
                    lean_inc_ref(v_arg_2290_);
                    v___x_2291_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2288_);
                    v___x_2292_ = l_Lean_Expr_isApp(v___x_2291_);
                    if v___x_2292_ == 0 {
                        lean_dec_ref(v___x_2291_);
                        lean_dec_ref(v_arg_2290_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_2293_ = lean_ctor_get(v___x_2291_, 1);
                        lean_inc_ref(v_arg_2293_);
                        v___x_2294_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2291_);
                        v___x_2295_ = l_Lean_Expr_isApp(v___x_2294_);
                        if v___x_2295_ == 0 {
                            lean_dec_ref(v___x_2294_);
                            lean_dec_ref(v_arg_2293_);
                            lean_dec_ref(v_arg_2290_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_2296_ = lean_ctor_get(v___x_2294_, 1);
                            lean_inc_ref(v_arg_2296_);
                            v___x_2297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2294_);
                            v___x_2298_ = l_Lean_Expr_isApp(v___x_2297_);
                            if v___x_2298_ == 0 {
                                lean_dec_ref(v___x_2297_);
                                lean_dec_ref(v_arg_2296_);
                                lean_dec_ref(v_arg_2293_);
                                lean_dec_ref(v_arg_2290_);
                                state = 2;
                                continue;
                            } else {
                                v___x_2299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2297_);
                                v___x_2300_ = l_Lean_Expr_isApp(v___x_2299_);
                                if v___x_2300_ == 0 {
                                    lean_dec_ref(v___x_2299_);
                                    lean_dec_ref(v_arg_2296_);
                                    lean_dec_ref(v_arg_2293_);
                                    lean_dec_ref(v_arg_2290_);
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2299_);
                                    v___x_2302_ = l_Lean_Expr_isApp(v___x_2301_);
                                    if v___x_2302_ == 0 {
                                        lean_dec_ref(v___x_2301_);
                                        lean_dec_ref(v_arg_2296_);
                                        lean_dec_ref(v_arg_2293_);
                                        lean_dec_ref(v_arg_2290_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_2303_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2301_);
                                        v___x_2304_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2;
                                        v___x_2305_ =
                                            l_Lean_Expr_isConstOf(v___x_2303_, v___x_2304_);
                                        if v___x_2305_ == 0 {
                                            lean_dec_ref(v_arg_2293_);
                                            v___x_2306_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5;
                                            v___x_2307_ =
                                                l_Lean_Expr_isConstOf(v___x_2303_, v___x_2306_);
                                            if v___x_2307_ == 0 {
                                                v___x_2308_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8;
                                                v___x_2309_ =
                                                    l_Lean_Expr_isConstOf(v___x_2303_, v___x_2308_);
                                                if v___x_2309_ == 0 {
                                                    lean_dec_ref(v_arg_2290_);
                                                    v___x_2310_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11;
                                                    v___x_2311_ = l_Lean_Expr_isConstOf(
                                                        v___x_2303_,
                                                        v___x_2310_,
                                                    );
                                                    lean_dec_ref(v___x_2303_);
                                                    if v___x_2311_ == 0 {
                                                        lean_dec_ref(v_arg_2296_);
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        lean_del_object(v___x_2280_);
                                                        v___x_2312_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_2296_, v_a_2273_);
                                                        return v___x_2312_;
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_2303_);
                                                    lean_del_object(v___x_2280_);
                                                    v___x_2313_ = l_Lean_Meta_getIntValue_x3f(
                                                        v_arg_2290_,
                                                        v_a_2272_,
                                                        v_a_2273_,
                                                        v_a_2274_,
                                                        v_a_2275_,
                                                    );
                                                    if lean_obj_tag(v___x_2313_) == 0 {
                                                        v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
                                                        v_isSharedCheck_2323_ =
                                                            (!lean_is_exclusive(v___x_2313_)) as u8;
                                                        if v_isSharedCheck_2323_ == 0 {
                                                            v___x_2316_ = v___x_2313_;
                                                            v_isShared_2317_ =
                                                                v_isSharedCheck_2323_;
                                                            state = 4;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_2314_);
                                                            lean_dec(v___x_2313_);
                                                            v___x_2316_ = lean_box(0);
                                                            v_isShared_2317_ =
                                                                v_isSharedCheck_2323_;
                                                            state = 4;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_2296_);
                                                        v_a_2324_ = lean_ctor_get(v___x_2313_, 0);
                                                        v_isSharedCheck_2331_ =
                                                            (!lean_is_exclusive(v___x_2313_)) as u8;
                                                        if v_isSharedCheck_2331_ == 0 {
                                                            v___x_2326_ = v___x_2313_;
                                                            v_isShared_2327_ =
                                                                v_isSharedCheck_2331_;
                                                            state = 6;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_2324_);
                                                            lean_dec(v___x_2313_);
                                                            v___x_2326_ = lean_box(0);
                                                            v_isShared_2327_ =
                                                                v_isSharedCheck_2331_;
                                                            state = 6;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_2303_);
                                                lean_del_object(v___x_2280_);
                                                v___x_2332_ = l_Lean_Meta_getIntValue_x3f(
                                                    v_arg_2290_,
                                                    v_a_2272_,
                                                    v_a_2273_,
                                                    v_a_2274_,
                                                    v_a_2275_,
                                                );
                                                if lean_obj_tag(v___x_2332_) == 0 {
                                                    v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
                                                    v_isSharedCheck_2342_ =
                                                        (!lean_is_exclusive(v___x_2332_)) as u8;
                                                    if v_isSharedCheck_2342_ == 0 {
                                                        v___x_2335_ = v___x_2332_;
                                                        v_isShared_2336_ = v_isSharedCheck_2342_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2333_);
                                                        lean_dec(v___x_2332_);
                                                        v___x_2335_ = lean_box(0);
                                                        v_isShared_2336_ = v_isSharedCheck_2342_;
                                                        state = 8;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_arg_2296_);
                                                    v_a_2343_ = lean_ctor_get(v___x_2332_, 0);
                                                    v_isSharedCheck_2350_ =
                                                        (!lean_is_exclusive(v___x_2332_)) as u8;
                                                    if v_isSharedCheck_2350_ == 0 {
                                                        v___x_2345_ = v___x_2332_;
                                                        v_isShared_2346_ = v_isSharedCheck_2350_;
                                                        state = 10;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2343_);
                                                        lean_dec(v___x_2332_);
                                                        v___x_2345_ = lean_box(0);
                                                        v_isShared_2346_ = v_isSharedCheck_2350_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_2303_);
                                            lean_del_object(v___x_2280_);
                                            v___x_2351_ =
                                                l_Lean_Meta_Structural_isInstHPowInt___redArg(
                                                    v_arg_2296_,
                                                    v_a_2273_,
                                                );
                                            if lean_obj_tag(v___x_2351_) == 0 {
                                                v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
                                                lean_inc(v_a_2352_);
                                                v___x_2353_ = (lean_unbox(v_a_2352_) as u8);
                                                if v___x_2353_ == 0 {
                                                    lean_dec(v_a_2352_);
                                                    lean_dec_ref(v_arg_2293_);
                                                    lean_dec_ref(v_arg_2290_);
                                                    return v___x_2351_;
                                                } else {
                                                    lean_dec_ref_known(v___x_2351_, 1);
                                                    v___x_2354_ = l_Lean_Meta_getIntValue_x3f(
                                                        v_arg_2293_,
                                                        v_a_2272_,
                                                        v_a_2273_,
                                                        v_a_2274_,
                                                        v_a_2275_,
                                                    );
                                                    if lean_obj_tag(v___x_2354_) == 0 {
                                                        v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
                                                        lean_inc(v_a_2355_);
                                                        lean_dec_ref_known(v___x_2354_, 1);
                                                        v___x_2356_ = l_Lean_Meta_getIntValue_x3f(
                                                            v_arg_2290_,
                                                            v_a_2272_,
                                                            v_a_2273_,
                                                            v_a_2274_,
                                                            v_a_2275_,
                                                        );
                                                        if lean_obj_tag(v___x_2356_) == 0 {
                                                            if lean_obj_tag(v_a_2355_) == 0 {
                                                                lean_dec(v_a_2352_);
                                                                v_isSharedCheck_2364_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_2356_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_2364_ == 0 {
                                                                    v_unused_2365_ = lean_ctor_get(
                                                                        v___x_2356_,
                                                                        0,
                                                                    );
                                                                    lean_dec(v_unused_2365_);
                                                                    v___x_2358_ = v___x_2356_;
                                                                    v_isShared_2359_ =
                                                                        v_isSharedCheck_2364_;
                                                                    state = 12;
                                                                    continue;
                                                                } else {
                                                                    lean_dec(v___x_2356_);
                                                                    v___x_2358_ = lean_box(0);
                                                                    v_isShared_2359_ =
                                                                        v_isSharedCheck_2364_;
                                                                    state = 12;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref_known(v_a_2355_, 1);
                                                                v_a_2366_ =
                                                                    lean_ctor_get(v___x_2356_, 0);
                                                                v_isSharedCheck_2378_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_2356_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_2378_ == 0 {
                                                                    v___x_2368_ = v___x_2356_;
                                                                    v_isShared_2369_ =
                                                                        v_isSharedCheck_2378_;
                                                                    state = 14;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_2366_);
                                                                    lean_dec(v___x_2356_);
                                                                    v___x_2368_ = lean_box(0);
                                                                    v_isShared_2369_ =
                                                                        v_isSharedCheck_2378_;
                                                                    state = 14;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec(v_a_2355_);
                                                            lean_dec(v_a_2352_);
                                                            v_a_2379_ =
                                                                lean_ctor_get(v___x_2356_, 0);
                                                            v_isSharedCheck_2386_ =
                                                                (!lean_is_exclusive(v___x_2356_))
                                                                    as u8;
                                                            if v_isSharedCheck_2386_ == 0 {
                                                                v___x_2381_ = v___x_2356_;
                                                                v_isShared_2382_ =
                                                                    v_isSharedCheck_2386_;
                                                                state = 17;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2379_);
                                                                lean_dec(v___x_2356_);
                                                                v___x_2381_ = lean_box(0);
                                                                v_isShared_2382_ =
                                                                    v_isSharedCheck_2386_;
                                                                state = 17;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec(v_a_2352_);
                                                        lean_dec_ref(v_arg_2290_);
                                                        v_a_2387_ = lean_ctor_get(v___x_2354_, 0);
                                                        v_isSharedCheck_2394_ =
                                                            (!lean_is_exclusive(v___x_2354_)) as u8;
                                                        if v_isSharedCheck_2394_ == 0 {
                                                            v___x_2389_ = v___x_2354_;
                                                            v_isShared_2390_ =
                                                                v_isSharedCheck_2394_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_2387_);
                                                            lean_dec(v___x_2354_);
                                                            v___x_2389_ = lean_box(0);
                                                            v_isShared_2390_ =
                                                                v_isSharedCheck_2394_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_2293_);
                                                lean_dec_ref(v_arg_2290_);
                                                return v___x_2351_;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2283_ = 0;
                v___x_2284_ = lean_box((v___x_2283_) as usize);
                if v_isShared_2281_ == 0 {
                    lean_ctor_set(v___x_2280_, 0, v___x_2284_);
                    v___x_2286_ = v___x_2280_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
                    v___x_2286_ = v_reuseFailAlloc_2287_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2286_;
            }
            4 => {
                if lean_obj_tag(v_a_2314_) == 0 {
                    lean_del_object(v___x_2316_);
                    v___x_2318_ =
                        l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_2296_, v_a_2273_);
                    return v___x_2318_;
                } else {
                    lean_dec_ref_known(v_a_2314_, 1);
                    lean_dec_ref(v_arg_2296_);
                    v___x_2319_ = lean_box((v___x_2307_) as usize);
                    if v_isShared_2317_ == 0 {
                        lean_ctor_set(v___x_2316_, 0, v___x_2319_);
                        v___x_2321_ = v___x_2316_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
                        v___x_2321_ = v_reuseFailAlloc_2322_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2321_;
            }
            6 => {
                if v_isShared_2327_ == 0 {
                    v___x_2329_ = v___x_2326_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
                    v___x_2329_ = v_reuseFailAlloc_2330_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2329_;
            }
            8 => {
                if lean_obj_tag(v_a_2333_) == 0 {
                    lean_del_object(v___x_2335_);
                    v___x_2337_ =
                        l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_2296_, v_a_2273_);
                    return v___x_2337_;
                } else {
                    lean_dec_ref_known(v_a_2333_, 1);
                    lean_dec_ref(v_arg_2296_);
                    v___x_2338_ = lean_box((v___x_2305_) as usize);
                    if v_isShared_2336_ == 0 {
                        lean_ctor_set(v___x_2335_, 0, v___x_2338_);
                        v___x_2340_ = v___x_2335_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
                        v___x_2340_ = v_reuseFailAlloc_2341_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_2340_;
            }
            10 => {
                if v_isShared_2346_ == 0 {
                    v___x_2348_ = v___x_2345_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
                    v___x_2348_ = v_reuseFailAlloc_2349_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2348_;
            }
            12 => {
                v___x_2360_ = lean_box((v___x_2305_) as usize);
                if v_isShared_2359_ == 0 {
                    lean_ctor_set(v___x_2358_, 0, v___x_2360_);
                    v___x_2362_ = v___x_2358_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
                    v___x_2362_ = v_reuseFailAlloc_2363_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2362_;
            }
            14 => {
                if lean_obj_tag(v_a_2366_) == 0 {
                    if v_isShared_2369_ == 0 {
                        lean_ctor_set(v___x_2368_, 0, v_a_2352_);
                        v___x_2371_ = v___x_2368_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2352_);
                        v___x_2371_ = v_reuseFailAlloc_2372_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_2366_, 1);
                    lean_dec(v_a_2352_);
                    v___x_2373_ = 0;
                    v___x_2374_ = lean_box((v___x_2373_) as usize);
                    if v_isShared_2369_ == 0 {
                        lean_ctor_set(v___x_2368_, 0, v___x_2374_);
                        v___x_2376_ = v___x_2368_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
                        v___x_2376_ = v_reuseFailAlloc_2377_;
                        state = 16;
                        continue;
                    }
                }
            }
            15 => {
                return v___x_2371_;
            }
            16 => {
                return v___x_2376_;
            }
            17 => {
                if v_isShared_2382_ == 0 {
                    v___x_2384_ = v___x_2381_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
                    v___x_2384_ = v_reuseFailAlloc_2385_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2384_;
            }
            19 => {
                if v_isShared_2390_ == 0 {
                    v___x_2392_ = v___x_2389_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
                    v___x_2392_ = v_reuseFailAlloc_2393_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2392_;
            }
            21 => {
                if v_isShared_2399_ == 0 {
                    v___x_2401_ = v___x_2398_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
                    v___x_2401_ = v_reuseFailAlloc_2402_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(
    mut v_e_2404_: *mut LeanObject,
    mut v_a_2405_: *mut LeanObject,
    mut v_a_2406_: *mut LeanObject,
    mut v_a_2407_: *mut LeanObject,
    mut v_a_2408_: *mut LeanObject,
    mut v_a_2409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2410_: *mut LeanObject = core::ptr::null_mut();
    v_res_2410_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
    lean_dec(v_a_2408_);
    lean_dec_ref(v_a_2407_);
    lean_dec(v_a_2406_);
    lean_dec_ref(v_a_2405_);
    return v_res_2410_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_x_2411_: *mut LeanObject,
    mut v_x_2412_: *mut LeanObject,
    mut v_x_2413_: *mut LeanObject,
    mut v_x_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: u8 = 0;
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2415_ = lean_ctor_get(v_x_2411_, 0);
                v_vs_2416_ = lean_ctor_get(v_x_2411_, 1);
                v_isSharedCheck_2440_ = (!lean_is_exclusive(v_x_2411_)) as u8;
                if v_isSharedCheck_2440_ == 0 {
                    v___x_2418_ = v_x_2411_;
                    v_isShared_2419_ = v_isSharedCheck_2440_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2416_);
                    lean_inc(v_ks_2415_);
                    lean_dec(v_x_2411_);
                    v___x_2418_ = lean_box(0);
                    v_isShared_2419_ = v_isSharedCheck_2440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2420_ = lean_array_get_size(v_ks_2415_);
                v___x_2421_ = lean_nat_dec_lt(v_x_2412_, v___x_2420_);
                if v___x_2421_ == 0 {
                    lean_dec(v_x_2412_);
                    v___x_2422_ = lean_array_push(v_ks_2415_, v_x_2413_);
                    v___x_2423_ = lean_array_push(v_vs_2416_, v_x_2414_);
                    if v_isShared_2419_ == 0 {
                        lean_ctor_set(v___x_2418_, 1, v___x_2423_);
                        lean_ctor_set(v___x_2418_, 0, v___x_2422_);
                        v___x_2425_ = v___x_2418_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2422_);
                        lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___x_2423_);
                        v___x_2425_ = v_reuseFailAlloc_2426_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2427_ = lean_array_fget_borrowed(v_ks_2415_, v_x_2412_);
                    v___x_2428_ = lean_nat_dec_eq(v_x_2413_, v_k_x27_2427_);
                    if v___x_2428_ == 0 {
                        if v_isShared_2419_ == 0 {
                            v___x_2430_ = v___x_2418_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_ks_2415_);
                            lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_vs_2416_);
                            v___x_2430_ = v_reuseFailAlloc_2434_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2435_ = lean_array_fset(v_ks_2415_, v_x_2412_, v_x_2413_);
                        v___x_2436_ = lean_array_fset(v_vs_2416_, v_x_2412_, v_x_2414_);
                        lean_dec(v_x_2412_);
                        if v_isShared_2419_ == 0 {
                            lean_ctor_set(v___x_2418_, 1, v___x_2436_);
                            lean_ctor_set(v___x_2418_, 0, v___x_2435_);
                            v___x_2438_ = v___x_2418_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2435_);
                            lean_ctor_set(v_reuseFailAlloc_2439_, 1, v___x_2436_);
                            v___x_2438_ = v_reuseFailAlloc_2439_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2425_;
            }
            3 => {
                v___x_2431_ = lean_unsigned_to_nat(1);
                v___x_2432_ = lean_nat_add(v_x_2412_, v___x_2431_);
                lean_dec(v_x_2412_);
                v_x_2411_ = v___x_2430_;
                v_x_2412_ = v___x_2432_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(
    mut v_n_2441_: *mut LeanObject,
    mut v_k_2442_: *mut LeanObject,
    mut v_v_2443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    v___x_2444_ = lean_unsigned_to_nat(0);
    v___x_2445_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3___redArg(v_n_2441_, v___x_2444_, v_k_2442_, v_v_2443_);
    return v___x_2445_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_2446_: usize = 0;
    let mut v___x_2447_: usize = 0;
    let mut v___x_2448_: usize = 0;
    v___x_2446_ = 5usize;
    v___x_2447_ = 1usize;
    v___x_2448_ = lean_usize_shift_left(v___x_2447_, v___x_2446_);
    return v___x_2448_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_2449_: usize = 0;
    let mut v___x_2450_: usize = 0;
    let mut v___x_2451_: usize = 0;
    v___x_2449_ = 1usize;
    v___x_2450_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
    v___x_2451_ = lean_usize_sub(v___x_2450_, v___x_2449_);
    return v___x_2451_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    v___x_2452_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2452_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(
    mut v_x_2453_: *mut LeanObject,
    mut v_x_2454_: usize,
    mut v_x_2455_: usize,
    mut v_x_2456_: *mut LeanObject,
    mut v_x_2457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: usize = 0;
    let mut v___x_2460_: usize = 0;
    let mut v___x_2461_: usize = 0;
    let mut v___x_2462_: usize = 0;
    let mut v_j_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2468_: u8 = 0;
    let mut v_v_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2482_: u8 = 0;
    let mut v___x_2483_: u8 = 0;
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2489_: u8 = 0;
    let mut v_node_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2493_: u8 = 0;
    let mut v___x_2494_: usize = 0;
    let mut v___x_2495_: usize = 0;
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2502_: u8 = 0;
    let mut v_unused_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2508_: u8 = 0;
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2513_: u8 = 0;
    let mut v_ks_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: usize = 0;
    let mut v___x_2520_: u8 = 0;
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: u8 = 0;
    let mut v_reuseFailAlloc_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2525_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2453_) == 0 {
                    v_es_2458_ = lean_ctor_get(v_x_2453_, 0);
                    v___x_2459_ = 5usize;
                    v___x_2460_ = 1usize;
                    v___x_2461_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
                    v___x_2462_ = lean_usize_land(v_x_2454_, v___x_2461_);
                    v_j_2463_ = lean_usize_to_nat(v___x_2462_);
                    v___x_2464_ = lean_array_get_size(v_es_2458_);
                    v___x_2465_ = lean_nat_dec_lt(v_j_2463_, v___x_2464_);
                    if v___x_2465_ == 0 {
                        lean_dec(v_j_2463_);
                        lean_dec(v_x_2457_);
                        lean_dec(v_x_2456_);
                        return v_x_2453_;
                    } else {
                        lean_inc_ref(v_es_2458_);
                        v_isSharedCheck_2502_ = (!lean_is_exclusive(v_x_2453_)) as u8;
                        if v_isSharedCheck_2502_ == 0 {
                            v_unused_2503_ = lean_ctor_get(v_x_2453_, 0);
                            lean_dec(v_unused_2503_);
                            v___x_2467_ = v_x_2453_;
                            v_isShared_2468_ = v_isSharedCheck_2502_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2453_);
                            v___x_2467_ = lean_box(0);
                            v_isShared_2468_ = v_isSharedCheck_2502_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2504_ = lean_ctor_get(v_x_2453_, 0);
                    v_vs_2505_ = lean_ctor_get(v_x_2453_, 1);
                    v_isSharedCheck_2525_ = (!lean_is_exclusive(v_x_2453_)) as u8;
                    if v_isSharedCheck_2525_ == 0 {
                        v___x_2507_ = v_x_2453_;
                        v_isShared_2508_ = v_isSharedCheck_2525_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2505_);
                        lean_inc(v_ks_2504_);
                        lean_dec(v_x_2453_);
                        v___x_2507_ = lean_box(0);
                        v_isShared_2508_ = v_isSharedCheck_2525_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2469_ = lean_array_fget(v_es_2458_, v_j_2463_);
                v___x_2470_ = lean_box(0);
                v_xs_x27_2471_ = lean_array_fset(v_es_2458_, v_j_2463_, v___x_2470_);
                match lean_obj_tag(v_v_2469_) {
                    0 => {
                        v_key_2478_ = lean_ctor_get(v_v_2469_, 0);
                        v_val_2479_ = lean_ctor_get(v_v_2469_, 1);
                        v_isSharedCheck_2489_ = (!lean_is_exclusive(v_v_2469_)) as u8;
                        if v_isSharedCheck_2489_ == 0 {
                            v___x_2481_ = v_v_2469_;
                            v_isShared_2482_ = v_isSharedCheck_2489_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2479_);
                            lean_inc(v_key_2478_);
                            lean_dec(v_v_2469_);
                            v___x_2481_ = lean_box(0);
                            v_isShared_2482_ = v_isSharedCheck_2489_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2490_ = lean_ctor_get(v_v_2469_, 0);
                        v_isSharedCheck_2500_ = (!lean_is_exclusive(v_v_2469_)) as u8;
                        if v_isSharedCheck_2500_ == 0 {
                            v___x_2492_ = v_v_2469_;
                            v_isShared_2493_ = v_isSharedCheck_2500_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2490_);
                            lean_dec(v_v_2469_);
                            v___x_2492_ = lean_box(0);
                            v_isShared_2493_ = v_isSharedCheck_2500_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2501_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2501_, 0, v_x_2456_);
                        lean_ctor_set(v___x_2501_, 1, v_x_2457_);
                        v___y_2473_ = v___x_2501_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2474_ = lean_array_fset(v_xs_x27_2471_, v_j_2463_, v___y_2473_);
                lean_dec(v_j_2463_);
                if v_isShared_2468_ == 0 {
                    lean_ctor_set(v___x_2467_, 0, v___x_2474_);
                    v___x_2476_ = v___x_2467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
                    v___x_2476_ = v_reuseFailAlloc_2477_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2476_;
            }
            4 => {
                v___x_2483_ = lean_nat_dec_eq(v_x_2456_, v_key_2478_);
                if v___x_2483_ == 0 {
                    lean_del_object(v___x_2481_);
                    v___x_2484_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2478_,
                        v_val_2479_,
                        v_x_2456_,
                        v_x_2457_,
                    );
                    v___x_2485_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2485_, 0, v___x_2484_);
                    v___y_2473_ = v___x_2485_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2479_);
                    lean_dec(v_key_2478_);
                    if v_isShared_2482_ == 0 {
                        lean_ctor_set(v___x_2481_, 1, v_x_2457_);
                        lean_ctor_set(v___x_2481_, 0, v_x_2456_);
                        v___x_2487_ = v___x_2481_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_x_2456_);
                        lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_x_2457_);
                        v___x_2487_ = v_reuseFailAlloc_2488_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2473_ = v___x_2487_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2494_ = lean_usize_shift_right(v_x_2454_, v___x_2459_);
                v___x_2495_ = lean_usize_add(v_x_2455_, v___x_2460_);
                v___x_2496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_node_2490_, v___x_2494_, v___x_2495_, v_x_2456_, v_x_2457_);
                if v_isShared_2493_ == 0 {
                    lean_ctor_set(v___x_2492_, 0, v___x_2496_);
                    v___x_2498_ = v___x_2492_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
                    v___x_2498_ = v_reuseFailAlloc_2499_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2473_ = v___x_2498_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2508_ == 0 {
                    v___x_2510_ = v___x_2507_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_ks_2504_);
                    lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_vs_2505_);
                    v___x_2510_ = v_reuseFailAlloc_2524_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2511_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v___x_2510_, v_x_2456_, v_x_2457_);
                v___x_2519_ = 7usize;
                v___x_2520_ = lean_usize_dec_le(v___x_2519_, v_x_2455_);
                if v___x_2520_ == 0 {
                    v___x_2521_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2511_);
                    v___x_2522_ = lean_unsigned_to_nat(4);
                    v___x_2523_ = lean_nat_dec_lt(v___x_2521_, v___x_2522_);
                    lean_dec(v___x_2521_);
                    v___y_2513_ = v___x_2523_;
                    state = 10;
                    continue;
                } else {
                    v___y_2513_ = v___x_2520_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2513_ == 0 {
                    v_ks_2514_ = lean_ctor_get(v_newNode_2511_, 0);
                    lean_inc_ref(v_ks_2514_);
                    v_vs_2515_ = lean_ctor_get(v_newNode_2511_, 1);
                    lean_inc_ref(v_vs_2515_);
                    lean_dec_ref(v_newNode_2511_);
                    v___x_2516_ = lean_unsigned_to_nat(0);
                    v___x_2517_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2);
                    v___x_2518_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_x_2455_, v_ks_2514_, v_vs_2515_, v___x_2516_, v___x_2517_);
                    lean_dec_ref(v_vs_2515_);
                    lean_dec_ref(v_ks_2514_);
                    return v___x_2518_;
                } else {
                    return v_newNode_2511_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(
    mut v_depth_2526_: usize,
    mut v_keys_2527_: *mut LeanObject,
    mut v_vals_2528_: *mut LeanObject,
    mut v_i_2529_: *mut LeanObject,
    mut v_entries_2530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: u8 = 0;
    let mut v_k_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u64 = 0;
    let mut v_h_2536_: usize = 0;
    let mut v___x_2537_: usize = 0;
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: usize = 0;
    let mut v___x_2540_: usize = 0;
    let mut v___x_2541_: usize = 0;
    let mut v_h_2542_: usize = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2531_ = lean_array_get_size(v_keys_2527_);
                v___x_2532_ = lean_nat_dec_lt(v_i_2529_, v___x_2531_);
                if v___x_2532_ == 0 {
                    lean_dec(v_i_2529_);
                    return v_entries_2530_;
                } else {
                    v_k_2533_ = lean_array_fget_borrowed(v_keys_2527_, v_i_2529_);
                    v_v_2534_ = lean_array_fget_borrowed(v_vals_2528_, v_i_2529_);
                    v___x_2535_ = lean_uint64_of_nat(v_k_2533_);
                    v_h_2536_ = lean_uint64_to_usize(v___x_2535_);
                    v___x_2537_ = 5usize;
                    v___x_2538_ = lean_unsigned_to_nat(1);
                    v___x_2539_ = 1usize;
                    v___x_2540_ = lean_usize_sub(v_depth_2526_, v___x_2539_);
                    v___x_2541_ = lean_usize_mul(v___x_2537_, v___x_2540_);
                    v_h_2542_ = lean_usize_shift_right(v_h_2536_, v___x_2541_);
                    v___x_2543_ = lean_nat_add(v_i_2529_, v___x_2538_);
                    lean_dec(v_i_2529_);
                    lean_inc(v_v_2534_);
                    lean_inc(v_k_2533_);
                    v___x_2544_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_entries_2530_, v_h_2542_, v_depth_2526_, v_k_2533_, v_v_2534_);
                    v_i_2529_ = v___x_2543_;
                    v_entries_2530_ = v___x_2544_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_2546_: *mut LeanObject,
    mut v_keys_2547_: *mut LeanObject,
    mut v_vals_2548_: *mut LeanObject,
    mut v_i_2549_: *mut LeanObject,
    mut v_entries_2550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2551_: usize = 0;
    let mut v_res_2552_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2551_ = lean_unbox_usize(v_depth_2546_);
    lean_dec(v_depth_2546_);
    v_res_2552_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2551_, v_keys_2547_, v_vals_2548_, v_i_2549_, v_entries_2550_);
    lean_dec_ref(v_vals_2548_);
    lean_dec_ref(v_keys_2547_);
    return v_res_2552_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___boxed(
    mut v_x_2553_: *mut LeanObject,
    mut v_x_2554_: *mut LeanObject,
    mut v_x_2555_: *mut LeanObject,
    mut v_x_2556_: *mut LeanObject,
    mut v_x_2557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9052__boxed_2558_: usize = 0;
    let mut v_x_9053__boxed_2559_: usize = 0;
    let mut v_res_2560_: *mut LeanObject = core::ptr::null_mut();
    v_x_9052__boxed_2558_ = lean_unbox_usize(v_x_2554_);
    lean_dec(v_x_2554_);
    v_x_9053__boxed_2559_ = lean_unbox_usize(v_x_2555_);
    lean_dec(v_x_2555_);
    v_res_2560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_2553_, v_x_9052__boxed_2558_, v_x_9053__boxed_2559_, v_x_2556_, v_x_2557_);
    return v_res_2560_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(
    mut v_x_2561_: *mut LeanObject,
    mut v_x_2562_: *mut LeanObject,
    mut v_x_2563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2564_: u64 = 0;
    let mut v___x_2565_: usize = 0;
    let mut v___x_2566_: usize = 0;
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    v___x_2564_ = lean_uint64_of_nat(v_x_2562_);
    v___x_2565_ = lean_uint64_to_usize(v___x_2564_);
    v___x_2566_ = 1usize;
    v___x_2567_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_2561_, v___x_2565_, v___x_2566_, v_x_2562_, v_x_2563_);
    return v___x_2567_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0(
    mut v_x_2568_: *mut LeanObject,
    mut v___y_2569_: *mut LeanObject,
    mut v_a_2570_: *mut LeanObject,
    mut v_s_2571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natDef_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dvds_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_2587_: u8 = 0;
    let mut v_conflict_x3f_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_divMod_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_2595_: u8 = 0;
    let mut v_nonlinearOccs_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2599_: u8 = 0;
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_2572_ = lean_ctor_get(v_s_2571_, 0);
                v_varMap_2573_ = lean_ctor_get(v_s_2571_, 1);
                v_vars_x27_2574_ = lean_ctor_get(v_s_2571_, 2);
                v_varMap_x27_2575_ = lean_ctor_get(v_s_2571_, 3);
                v_natToIntMap_2576_ = lean_ctor_get(v_s_2571_, 4);
                v_natDef_2577_ = lean_ctor_get(v_s_2571_, 5);
                v_dvds_2578_ = lean_ctor_get(v_s_2571_, 6);
                v_lowers_2579_ = lean_ctor_get(v_s_2571_, 7);
                v_uppers_2580_ = lean_ctor_get(v_s_2571_, 8);
                v_diseqs_2581_ = lean_ctor_get(v_s_2571_, 9);
                v_elimEqs_2582_ = lean_ctor_get(v_s_2571_, 10);
                v_elimStack_2583_ = lean_ctor_get(v_s_2571_, 11);
                v_occurs_2584_ = lean_ctor_get(v_s_2571_, 12);
                v_assignment_2585_ = lean_ctor_get(v_s_2571_, 13);
                v_nextCnstrId_2586_ = lean_ctor_get(v_s_2571_, 14);
                v_caseSplits_2587_ = lean_ctor_get_uint8(
                    v_s_2571_,
                    (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_2588_ = lean_ctor_get(v_s_2571_, 15);
                v_diseqSplits_2589_ = lean_ctor_get(v_s_2571_, 16);
                v_divMod_2590_ = lean_ctor_get(v_s_2571_, 17);
                v_toIntIds_2591_ = lean_ctor_get(v_s_2571_, 18);
                v_toIntInfos_2592_ = lean_ctor_get(v_s_2571_, 19);
                v_toIntTermMap_2593_ = lean_ctor_get(v_s_2571_, 20);
                v_toIntVarMap_2594_ = lean_ctor_get(v_s_2571_, 21);
                v_usedCommRing_2595_ = lean_ctor_get_uint8(
                    v_s_2571_,
                    (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_2596_ = lean_ctor_get(v_s_2571_, 22);
                v_isSharedCheck_2605_ = (!lean_is_exclusive(v_s_2571_)) as u8;
                if v_isSharedCheck_2605_ == 0 {
                    v___x_2598_ = v_s_2571_;
                    v_isShared_2599_ = v_isSharedCheck_2605_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nonlinearOccs_2596_);
                    lean_inc(v_toIntVarMap_2594_);
                    lean_inc(v_toIntTermMap_2593_);
                    lean_inc(v_toIntInfos_2592_);
                    lean_inc(v_toIntIds_2591_);
                    lean_inc(v_divMod_2590_);
                    lean_inc(v_diseqSplits_2589_);
                    lean_inc(v_conflict_x3f_2588_);
                    lean_inc(v_nextCnstrId_2586_);
                    lean_inc(v_assignment_2585_);
                    lean_inc(v_occurs_2584_);
                    lean_inc(v_elimStack_2583_);
                    lean_inc(v_elimEqs_2582_);
                    lean_inc(v_diseqs_2581_);
                    lean_inc(v_uppers_2580_);
                    lean_inc(v_lowers_2579_);
                    lean_inc(v_dvds_2578_);
                    lean_inc(v_natDef_2577_);
                    lean_inc(v_natToIntMap_2576_);
                    lean_inc(v_varMap_x27_2575_);
                    lean_inc(v_vars_x27_2574_);
                    lean_inc(v_varMap_2573_);
                    lean_inc(v_vars_2572_);
                    lean_dec(v_s_2571_);
                    v___x_2598_ = lean_box(0);
                    v_isShared_2599_ = v_isSharedCheck_2605_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2600_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2600_, 0, v_x_2568_);
                lean_ctor_set(v___x_2600_, 1, v___y_2569_);
                v___x_2601_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_nonlinearOccs_2596_, v_a_2570_, v___x_2600_);
                if v_isShared_2599_ == 0 {
                    lean_ctor_set(v___x_2598_, 22, v___x_2601_);
                    v___x_2603_ = v___x_2598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 23, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_vars_2572_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_varMap_2573_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_vars_x27_2574_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_varMap_x27_2575_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_natToIntMap_2576_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 5, v_natDef_2577_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 6, v_dvds_2578_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 7, v_lowers_2579_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 8, v_uppers_2580_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 9, v_diseqs_2581_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 10, v_elimEqs_2582_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 11, v_elimStack_2583_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 12, v_occurs_2584_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 13, v_assignment_2585_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 14, v_nextCnstrId_2586_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 15, v_conflict_x3f_2588_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 16, v_diseqSplits_2589_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 17, v_divMod_2590_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 18, v_toIntIds_2591_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 19, v_toIntInfos_2592_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 20, v_toIntTermMap_2593_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 21, v_toIntVarMap_2594_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 22, v___x_2601_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2604_,
                        (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                        v_caseSplits_2587_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2604_,
                        (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_2595_,
                    );
                    v___x_2603_ = v_reuseFailAlloc_2604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(
    mut v_keys_2606_: *mut LeanObject,
    mut v_vals_2607_: *mut LeanObject,
    mut v_i_2608_: *mut LeanObject,
    mut v_k_2609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: u8 = 0;
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2610_ = lean_array_get_size(v_keys_2606_);
                v___x_2611_ = lean_nat_dec_lt(v_i_2608_, v___x_2610_);
                if v___x_2611_ == 0 {
                    lean_dec(v_i_2608_);
                    v___x_2612_ = lean_box(0);
                    return v___x_2612_;
                } else {
                    v_k_x27_2613_ = lean_array_fget_borrowed(v_keys_2606_, v_i_2608_);
                    v___x_2614_ = lean_nat_dec_eq(v_k_2609_, v_k_x27_2613_);
                    if v___x_2614_ == 0 {
                        v___x_2615_ = lean_unsigned_to_nat(1);
                        v___x_2616_ = lean_nat_add(v_i_2608_, v___x_2615_);
                        lean_dec(v_i_2608_);
                        v_i_2608_ = v___x_2616_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2618_ = lean_array_fget_borrowed(v_vals_2607_, v_i_2608_);
                        lean_dec(v_i_2608_);
                        lean_inc(v___x_2618_);
                        v___x_2619_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2619_, 0, v___x_2618_);
                        return v___x_2619_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_keys_2620_: *mut LeanObject,
    mut v_vals_2621_: *mut LeanObject,
    mut v_i_2622_: *mut LeanObject,
    mut v_k_2623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2624_: *mut LeanObject = core::ptr::null_mut();
    v_res_2624_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_keys_2620_, v_vals_2621_, v_i_2622_, v_k_2623_);
    lean_dec(v_k_2623_);
    lean_dec_ref(v_vals_2621_);
    lean_dec_ref(v_keys_2620_);
    return v_res_2624_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(
    mut v_x_2625_: *mut LeanObject,
    mut v_x_2626_: usize,
    mut v_x_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: usize = 0;
    let mut v___x_2631_: usize = 0;
    let mut v___x_2632_: usize = 0;
    let mut v_j_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: u8 = 0;
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: usize = 0;
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2625_) == 0 {
                    v_es_2628_ = lean_ctor_get(v_x_2625_, 0);
                    v___x_2629_ = lean_box(2);
                    v___x_2630_ = 5usize;
                    v___x_2631_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
                    v___x_2632_ = lean_usize_land(v_x_2626_, v___x_2631_);
                    v_j_2633_ = lean_usize_to_nat(v___x_2632_);
                    v___x_2634_ = lean_array_get_borrowed(v___x_2629_, v_es_2628_, v_j_2633_);
                    lean_dec(v_j_2633_);
                    match lean_obj_tag(v___x_2634_) {
                        0 => {
                            v_key_2635_ = lean_ctor_get(v___x_2634_, 0);
                            v_val_2636_ = lean_ctor_get(v___x_2634_, 1);
                            v___x_2637_ = lean_nat_dec_eq(v_x_2627_, v_key_2635_);
                            if v___x_2637_ == 0 {
                                v___x_2638_ = lean_box(0);
                                return v___x_2638_;
                            } else {
                                lean_inc(v_val_2636_);
                                v___x_2639_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2639_, 0, v_val_2636_);
                                return v___x_2639_;
                            }
                        }
                        1 => {
                            v_node_2640_ = lean_ctor_get(v___x_2634_, 0);
                            v___x_2641_ = lean_usize_shift_right(v_x_2626_, v___x_2630_);
                            v_x_2625_ = v_node_2640_;
                            v_x_2626_ = v___x_2641_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2643_ = lean_box(0);
                            return v___x_2643_;
                        }
                    }
                } else {
                    v_ks_2644_ = lean_ctor_get(v_x_2625_, 0);
                    v_vs_2645_ = lean_ctor_get(v_x_2625_, 1);
                    v___x_2646_ = lean_unsigned_to_nat(0);
                    v___x_2647_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_ks_2644_, v_vs_2645_, v___x_2646_, v_x_2627_);
                    return v___x_2647_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg___boxed(
    mut v_x_2648_: *mut LeanObject,
    mut v_x_2649_: *mut LeanObject,
    mut v_x_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9274__boxed_2651_: usize = 0;
    let mut v_res_2652_: *mut LeanObject = core::ptr::null_mut();
    v_x_9274__boxed_2651_ = lean_unbox_usize(v_x_2649_);
    lean_dec(v_x_2649_);
    v_res_2652_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_2648_, v_x_9274__boxed_2651_, v_x_2650_);
    lean_dec(v_x_2650_);
    lean_dec_ref(v_x_2648_);
    return v_res_2652_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(
    mut v_x_2653_: *mut LeanObject,
    mut v_x_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2655_: u64 = 0;
    let mut v___x_2656_: usize = 0;
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    v___x_2655_ = lean_uint64_of_nat(v_x_2654_);
    v___x_2656_ = lean_uint64_to_usize(v___x_2655_);
    v___x_2657_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_2653_, v___x_2656_, v_x_2654_);
    return v___x_2657_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg___boxed(
    mut v_x_2658_: *mut LeanObject,
    mut v_x_2659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2660_: *mut LeanObject = core::ptr::null_mut();
    v_res_2660_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_x_2658_, v_x_2659_);
    lean_dec(v_x_2659_);
    lean_dec_ref(v_x_2658_);
    return v_res_2660_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0()
-> *mut LeanObject {
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2662_: *mut LeanObject = core::ptr::null_mut();
    v___x_2661_ = lean_alloc_closure(l_instDecidableEqNat___boxed as *mut core::ffi::c_void, 2, 0);
    v___f_2662_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2662_, 0, v___x_2661_);
    return v___f_2662_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(
    mut v_arg_2663_: *mut LeanObject,
    mut v_x_2664_: *mut LeanObject,
    mut v_a_2665_: *mut LeanObject,
    mut v_a_2666_: *mut LeanObject,
    mut v_a_2667_: *mut LeanObject,
    mut v_a_2668_: *mut LeanObject,
    mut v_a_2669_: *mut LeanObject,
    mut v_a_2670_: *mut LeanObject,
    mut v_a_2671_: *mut LeanObject,
    mut v_a_2672_: *mut LeanObject,
    mut v_a_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2680_: u8 = 0;
    let mut v___y_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: u8 = 0;
    let mut v___f_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nonlinearOccs_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2710_: u8 = 0;
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2720_: u8 = 0;
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2725_: u8 = 0;
    let mut v_a_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2729_: u8 = 0;
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2733_: u8 = 0;
    let mut v_elimEqs_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: u8 = 0;
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2743_: u8 = 0;
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2747_: u8 = 0;
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut v_a_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2674_);
                lean_inc_ref(v_a_2673_);
                lean_inc(v_a_2672_);
                lean_inc_ref(v_a_2671_);
                lean_inc(v_a_2670_);
                lean_inc_ref(v_a_2669_);
                lean_inc(v_a_2668_);
                lean_inc_ref(v_a_2667_);
                lean_inc(v_a_2666_);
                lean_inc(v_a_2665_);
                v___x_2676_ = lean_grind_cutsat_mk_var(
                    v_arg_2663_,
                    v_a_2665_,
                    v_a_2666_,
                    v_a_2667_,
                    v_a_2668_,
                    v_a_2669_,
                    v_a_2670_,
                    v_a_2671_,
                    v_a_2672_,
                    v_a_2673_,
                    v_a_2674_,
                );
                if lean_obj_tag(v___x_2676_) == 0 {
                    v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
                    v_isSharedCheck_2748_ = (!lean_is_exclusive(v___x_2676_)) as u8;
                    if v_isSharedCheck_2748_ == 0 {
                        v___x_2679_ = v___x_2676_;
                        v_isShared_2680_ = v_isSharedCheck_2748_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2677_);
                        lean_dec(v___x_2676_);
                        v___x_2679_ = lean_box(0);
                        v_isShared_2680_ = v_isSharedCheck_2748_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x_2664_);
                    v_a_2749_ = lean_ctor_get(v___x_2676_, 0);
                    v_isSharedCheck_2756_ = (!lean_is_exclusive(v___x_2676_)) as u8;
                    if v_isSharedCheck_2756_ == 0 {
                        v___x_2751_ = v___x_2676_;
                        v_isShared_2752_ = v_isSharedCheck_2756_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2749_);
                        lean_dec(v___x_2676_);
                        v___x_2751_ = lean_box(0);
                        v_isShared_2752_ = v_isSharedCheck_2756_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2711_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2665_, v_a_2673_);
                if lean_obj_tag(v___x_2711_) == 0 {
                    v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
                    lean_inc(v_a_2712_);
                    lean_dec_ref_known(v___x_2711_, 1);
                    v_elimEqs_2734_ = lean_ctor_get(v_a_2712_, 10);
                    lean_inc_ref(v_elimEqs_2734_);
                    lean_dec(v_a_2712_);
                    v_size_2735_ = lean_ctor_get(v_elimEqs_2734_, 2);
                    v___x_2736_ = lean_box(0);
                    v___x_2737_ = lean_nat_dec_lt(v_a_2677_, v_size_2735_);
                    if v___x_2737_ == 0 {
                        lean_dec_ref(v_elimEqs_2734_);
                        v___x_2738_ = l_outOfBounds___redArg(v___x_2736_);
                        v___y_2714_ = v___x_2738_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2739_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_2736_,
                            v_elimEqs_2734_,
                            v_a_2677_,
                        );
                        lean_dec_ref(v_elimEqs_2734_);
                        v___y_2714_ = v___x_2739_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2679_);
                    lean_dec(v_a_2677_);
                    lean_dec(v_x_2664_);
                    v_a_2740_ = lean_ctor_get(v___x_2711_, 0);
                    v_isSharedCheck_2747_ = (!lean_is_exclusive(v___x_2711_)) as u8;
                    if v_isSharedCheck_2747_ == 0 {
                        v___x_2742_ = v___x_2711_;
                        v_isShared_2743_ = v_isSharedCheck_2747_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_2740_);
                        lean_dec(v___x_2711_);
                        v___x_2742_ = lean_box(0);
                        v_isShared_2743_ = v_isSharedCheck_2747_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v___y_2684_);
                lean_inc(v_x_2664_);
                lean_inc_ref(v___y_2683_);
                v___x_2685_ = l_List_elem___redArg(v___y_2683_, v_x_2664_, v___y_2684_);
                if v___x_2685_ == 0 {
                    lean_del_object(v___x_2679_);
                    v___f_2686_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0 as *mut core::ffi::c_void, 4, 3);
                    lean_closure_set(v___f_2686_, 0, v_x_2664_);
                    lean_closure_set(v___f_2686_, 1, v___y_2684_);
                    lean_closure_set(v___f_2686_, 2, v_a_2677_);
                    v___x_2687_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_2688_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2687_, v___f_2686_, v___y_2682_);
                    return v___x_2688_;
                } else {
                    lean_dec(v___y_2684_);
                    lean_dec(v_a_2677_);
                    lean_dec(v_x_2664_);
                    v___x_2689_ = lean_box(0);
                    if v_isShared_2680_ == 0 {
                        lean_ctor_set(v___x_2679_, 0, v___x_2689_);
                        v___x_2691_ = v___x_2679_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
                        v___x_2691_ = v_reuseFailAlloc_2692_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2691_;
            }
            4 => {
                v___x_2696_ =
                    l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_2694_, v___y_2695_);
                if lean_obj_tag(v___x_2696_) == 0 {
                    v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
                    lean_inc(v_a_2697_);
                    lean_dec_ref_known(v___x_2696_, 1);
                    v_nonlinearOccs_2698_ = lean_ctor_get(v_a_2697_, 22);
                    lean_inc_ref(v_nonlinearOccs_2698_);
                    lean_dec(v_a_2697_);
                    v___f_2699_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0);
                    v___x_2700_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_nonlinearOccs_2698_, v_a_2677_);
                    lean_dec_ref(v_nonlinearOccs_2698_);
                    if lean_obj_tag(v___x_2700_) == 0 {
                        v___x_2701_ = lean_box(0);
                        v___y_2682_ = v___y_2694_;
                        v___y_2683_ = v___f_2699_;
                        v___y_2684_ = v___x_2701_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2702_ = lean_ctor_get(v___x_2700_, 0);
                        lean_inc(v_val_2702_);
                        lean_dec_ref_known(v___x_2700_, 1);
                        v___y_2682_ = v___y_2694_;
                        v___y_2683_ = v___f_2699_;
                        v___y_2684_ = v_val_2702_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2679_);
                    lean_dec(v_a_2677_);
                    lean_dec(v_x_2664_);
                    v_a_2703_ = lean_ctor_get(v___x_2696_, 0);
                    v_isSharedCheck_2710_ = (!lean_is_exclusive(v___x_2696_)) as u8;
                    if v_isSharedCheck_2710_ == 0 {
                        v___x_2705_ = v___x_2696_;
                        v_isShared_2706_ = v_isSharedCheck_2710_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2703_);
                        lean_dec(v___x_2696_);
                        v___x_2705_ = lean_box(0);
                        v_isShared_2706_ = v_isSharedCheck_2710_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_2706_ == 0 {
                    v___x_2708_ = v___x_2705_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
                    v___x_2708_ = v_reuseFailAlloc_2709_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2708_;
            }
            7 => {
                if lean_obj_tag(v___y_2714_) == 0 {
                    v___y_2694_ = v_a_2665_;
                    v___y_2695_ = v_a_2673_;
                    state = 4;
                    continue;
                } else {
                    lean_dec_ref_known(v___y_2714_, 1);
                    lean_inc(v_a_2674_);
                    lean_inc_ref(v_a_2673_);
                    lean_inc(v_a_2672_);
                    lean_inc_ref(v_a_2671_);
                    lean_inc(v_a_2670_);
                    lean_inc_ref(v_a_2669_);
                    lean_inc(v_a_2668_);
                    lean_inc_ref(v_a_2667_);
                    lean_inc(v_a_2666_);
                    lean_inc(v_a_2665_);
                    lean_inc(v_x_2664_);
                    lean_inc(v_a_2677_);
                    v___x_2715_ = lean_cutsat_propagate_nonlinear(
                        v_a_2677_, v_x_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_,
                        v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_,
                    );
                    if lean_obj_tag(v___x_2715_) == 0 {
                        v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
                        v_isSharedCheck_2725_ = (!lean_is_exclusive(v___x_2715_)) as u8;
                        if v_isSharedCheck_2725_ == 0 {
                            v___x_2718_ = v___x_2715_;
                            v_isShared_2719_ = v_isSharedCheck_2725_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2716_);
                            lean_dec(v___x_2715_);
                            v___x_2718_ = lean_box(0);
                            v_isShared_2719_ = v_isSharedCheck_2725_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2679_);
                        lean_dec(v_a_2677_);
                        lean_dec(v_x_2664_);
                        v_a_2726_ = lean_ctor_get(v___x_2715_, 0);
                        v_isSharedCheck_2733_ = (!lean_is_exclusive(v___x_2715_)) as u8;
                        if v_isSharedCheck_2733_ == 0 {
                            v___x_2728_ = v___x_2715_;
                            v_isShared_2729_ = v_isSharedCheck_2733_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2726_);
                            lean_dec(v___x_2715_);
                            v___x_2728_ = lean_box(0);
                            v_isShared_2729_ = v_isSharedCheck_2733_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            8 => {
                v___x_2720_ = (lean_unbox(v_a_2716_) as u8);
                lean_dec(v_a_2716_);
                if v___x_2720_ == 0 {
                    lean_del_object(v___x_2718_);
                    v___y_2694_ = v_a_2665_;
                    v___y_2695_ = v_a_2673_;
                    state = 4;
                    continue;
                } else {
                    lean_del_object(v___x_2679_);
                    lean_dec(v_a_2677_);
                    lean_dec(v_x_2664_);
                    v___x_2721_ = lean_box(0);
                    if v_isShared_2719_ == 0 {
                        lean_ctor_set(v___x_2718_, 0, v___x_2721_);
                        v___x_2723_ = v___x_2718_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
                        v___x_2723_ = v_reuseFailAlloc_2724_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_2723_;
            }
            10 => {
                if v_isShared_2729_ == 0 {
                    v___x_2731_ = v___x_2728_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
                    v___x_2731_ = v_reuseFailAlloc_2732_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2731_;
            }
            12 => {
                if v_isShared_2743_ == 0 {
                    v___x_2745_ = v___x_2742_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
                    v___x_2745_ = v_reuseFailAlloc_2746_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2745_;
            }
            14 => {
                if v_isShared_2752_ == 0 {
                    v___x_2754_ = v___x_2751_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
                    v___x_2754_ = v_reuseFailAlloc_2755_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___boxed(
    mut v_arg_2757_: *mut LeanObject,
    mut v_x_2758_: *mut LeanObject,
    mut v_a_2759_: *mut LeanObject,
    mut v_a_2760_: *mut LeanObject,
    mut v_a_2761_: *mut LeanObject,
    mut v_a_2762_: *mut LeanObject,
    mut v_a_2763_: *mut LeanObject,
    mut v_a_2764_: *mut LeanObject,
    mut v_a_2765_: *mut LeanObject,
    mut v_a_2766_: *mut LeanObject,
    mut v_a_2767_: *mut LeanObject,
    mut v_a_2768_: *mut LeanObject,
    mut v_a_2769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2770_: *mut LeanObject = core::ptr::null_mut();
    v_res_2770_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_2757_, v_x_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
    lean_dec(v_a_2768_);
    lean_dec_ref(v_a_2767_);
    lean_dec(v_a_2766_);
    lean_dec_ref(v_a_2765_);
    lean_dec(v_a_2764_);
    lean_dec_ref(v_a_2763_);
    lean_dec(v_a_2762_);
    lean_dec_ref(v_a_2761_);
    lean_dec(v_a_2760_);
    lean_dec(v_a_2759_);
    return v_res_2770_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0(
    mut v_00_u03b2_2771_: *mut LeanObject,
    mut v_x_2772_: *mut LeanObject,
    mut v_x_2773_: *mut LeanObject,
    mut v_x_2774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    v___x_2775_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_x_2772_, v_x_2773_, v_x_2774_);
    return v___x_2775_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(
    mut v_00_u03b2_2776_: *mut LeanObject,
    mut v_x_2777_: *mut LeanObject,
    mut v_x_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    v___x_2779_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_x_2777_, v_x_2778_);
    return v___x_2779_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(
    mut v_00_u03b2_2780_: *mut LeanObject,
    mut v_x_2781_: *mut LeanObject,
    mut v_x_2782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2783_: *mut LeanObject = core::ptr::null_mut();
    v_res_2783_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_00_u03b2_2780_, v_x_2781_, v_x_2782_);
    lean_dec(v_x_2782_);
    lean_dec_ref(v_x_2781_);
    return v_res_2783_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(
    mut v_00_u03b2_2784_: *mut LeanObject,
    mut v_x_2785_: *mut LeanObject,
    mut v_x_2786_: usize,
    mut v_x_2787_: usize,
    mut v_x_2788_: *mut LeanObject,
    mut v_x_2789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    v___x_2790_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_2785_, v_x_2786_, v_x_2787_, v_x_2788_, v_x_2789_);
    return v___x_2790_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(
    mut v_00_u03b2_2791_: *mut LeanObject,
    mut v_x_2792_: *mut LeanObject,
    mut v_x_2793_: *mut LeanObject,
    mut v_x_2794_: *mut LeanObject,
    mut v_x_2795_: *mut LeanObject,
    mut v_x_2796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9517__boxed_2797_: usize = 0;
    let mut v_x_9518__boxed_2798_: usize = 0;
    let mut v_res_2799_: *mut LeanObject = core::ptr::null_mut();
    v_x_9517__boxed_2797_ = lean_unbox_usize(v_x_2793_);
    lean_dec(v_x_2793_);
    v_x_9518__boxed_2798_ = lean_unbox_usize(v_x_2794_);
    lean_dec(v_x_2794_);
    v_res_2799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_2791_, v_x_2792_, v_x_9517__boxed_2797_, v_x_9518__boxed_2798_, v_x_2795_, v_x_2796_);
    return v_res_2799_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(
    mut v_00_u03b2_2800_: *mut LeanObject,
    mut v_x_2801_: *mut LeanObject,
    mut v_x_2802_: usize,
    mut v_x_2803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    v___x_2804_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_2801_, v_x_2802_, v_x_2803_);
    return v___x_2804_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___boxed(
    mut v_00_u03b2_2805_: *mut LeanObject,
    mut v_x_2806_: *mut LeanObject,
    mut v_x_2807_: *mut LeanObject,
    mut v_x_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9534__boxed_2809_: usize = 0;
    let mut v_res_2810_: *mut LeanObject = core::ptr::null_mut();
    v_x_9534__boxed_2809_ = lean_unbox_usize(v_x_2807_);
    lean_dec(v_x_2807_);
    v_res_2810_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(v_00_u03b2_2805_, v_x_2806_, v_x_9534__boxed_2809_, v_x_2808_);
    lean_dec(v_x_2808_);
    lean_dec_ref(v_x_2806_);
    return v_res_2810_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2811_: *mut LeanObject,
    mut v_n_2812_: *mut LeanObject,
    mut v_k_2813_: *mut LeanObject,
    mut v_v_2814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    v___x_2815_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v_n_2812_, v_k_2813_, v_v_2814_);
    return v___x_2815_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2816_: *mut LeanObject,
    mut v_depth_2817_: usize,
    mut v_keys_2818_: *mut LeanObject,
    mut v_vals_2819_: *mut LeanObject,
    mut v_heq_2820_: *mut LeanObject,
    mut v_i_2821_: *mut LeanObject,
    mut v_entries_2822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    v___x_2823_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_2817_, v_keys_2818_, v_vals_2819_, v_i_2821_, v_entries_2822_);
    return v___x_2823_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2824_: *mut LeanObject,
    mut v_depth_2825_: *mut LeanObject,
    mut v_keys_2826_: *mut LeanObject,
    mut v_vals_2827_: *mut LeanObject,
    mut v_heq_2828_: *mut LeanObject,
    mut v_i_2829_: *mut LeanObject,
    mut v_entries_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2831_: usize = 0;
    let mut v_res_2832_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2831_ = lean_unbox_usize(v_depth_2825_);
    lean_dec(v_depth_2825_);
    v_res_2832_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(v_00_u03b2_2824_, v_depth_boxed_2831_, v_keys_2826_, v_vals_2827_, v_heq_2828_, v_i_2829_, v_entries_2830_);
    lean_dec_ref(v_vals_2827_);
    lean_dec_ref(v_keys_2826_);
    return v_res_2832_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2833_: *mut LeanObject,
    mut v_keys_2834_: *mut LeanObject,
    mut v_vals_2835_: *mut LeanObject,
    mut v_heq_2836_: *mut LeanObject,
    mut v_i_2837_: *mut LeanObject,
    mut v_k_2838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    v___x_2839_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_keys_2834_, v_vals_2835_, v_i_2837_, v_k_2838_);
    return v___x_2839_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_2840_: *mut LeanObject,
    mut v_keys_2841_: *mut LeanObject,
    mut v_vals_2842_: *mut LeanObject,
    mut v_heq_2843_: *mut LeanObject,
    mut v_i_2844_: *mut LeanObject,
    mut v_k_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2846_: *mut LeanObject = core::ptr::null_mut();
    v_res_2846_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(v_00_u03b2_2840_, v_keys_2841_, v_vals_2842_, v_heq_2843_, v_i_2844_, v_k_2845_);
    lean_dec(v_k_2845_);
    lean_dec_ref(v_vals_2842_);
    lean_dec_ref(v_keys_2841_);
    return v_res_2846_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2847_: *mut LeanObject,
    mut v_x_2848_: *mut LeanObject,
    mut v_x_2849_: *mut LeanObject,
    mut v_x_2850_: *mut LeanObject,
    mut v_x_2851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    v___x_2852_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2848_, v_x_2849_, v_x_2850_, v_x_2851_);
    return v___x_2852_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(
    mut v_x_2853_: *mut LeanObject,
    mut v_e_2854_: *mut LeanObject,
    mut v_a_2855_: *mut LeanObject,
    mut v_a_2856_: *mut LeanObject,
    mut v_a_2857_: *mut LeanObject,
    mut v_a_2858_: *mut LeanObject,
    mut v_a_2859_: *mut LeanObject,
    mut v_a_2860_: *mut LeanObject,
    mut v_a_2861_: *mut LeanObject,
    mut v_a_2862_: *mut LeanObject,
    mut v_a_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: u8 = 0;
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: u8 = 0;
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: u8 = 0;
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: u8 = 0;
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v_a_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2910_: u8 = 0;
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2914_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_2854_);
                v___x_2866_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2854_, v_a_2862_);
                if lean_obj_tag(v___x_2866_) == 0 {
                    v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
                    lean_inc(v_a_2867_);
                    lean_dec_ref_known(v___x_2866_, 1);
                    v___x_2868_ = l_Lean_Expr_cleanupAnnotations(v_a_2867_);
                    v___x_2869_ = l_Lean_Expr_isApp(v___x_2868_);
                    if v___x_2869_ == 0 {
                        lean_dec_ref(v___x_2868_);
                        v___x_2870_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_2854_, v_x_2853_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
                        return v___x_2870_;
                    } else {
                        v_arg_2871_ = lean_ctor_get(v___x_2868_, 1);
                        lean_inc_ref(v_arg_2871_);
                        v___x_2872_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2868_);
                        v___x_2873_ = l_Lean_Expr_isApp(v___x_2872_);
                        if v___x_2873_ == 0 {
                            lean_dec_ref(v___x_2872_);
                            lean_dec_ref(v_arg_2871_);
                            v___x_2874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_2854_, v_x_2853_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
                            return v___x_2874_;
                        } else {
                            v_arg_2875_ = lean_ctor_get(v___x_2872_, 1);
                            lean_inc_ref(v_arg_2875_);
                            v___x_2876_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2872_);
                            v___x_2877_ = l_Lean_Expr_isApp(v___x_2876_);
                            if v___x_2877_ == 0 {
                                lean_dec_ref(v___x_2876_);
                                lean_dec_ref(v_arg_2875_);
                                lean_dec_ref(v_arg_2871_);
                                v___x_2878_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_2854_, v_x_2853_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
                                return v___x_2878_;
                            } else {
                                v_arg_2879_ = lean_ctor_get(v___x_2876_, 1);
                                lean_inc_ref(v_arg_2879_);
                                v___x_2880_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2876_);
                                v___x_2881_ = l_Lean_Expr_isApp(v___x_2880_);
                                if v___x_2881_ == 0 {
                                    lean_dec_ref(v___x_2880_);
                                    lean_dec_ref(v_arg_2879_);
                                    lean_dec_ref(v_arg_2875_);
                                    lean_dec_ref(v_arg_2871_);
                                    v___x_2882_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_2854_, v_x_2853_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
                                    return v___x_2882_;
                                } else {
                                    v___x_2883_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2880_);
                                    v___x_2884_ = l_Lean_Expr_isApp(v___x_2883_);
                                    if v___x_2884_ == 0 {
                                        lean_dec_ref(v___x_2883_);
                                        lean_dec_ref(v_arg_2879_);
                                        lean_dec_ref(v_arg_2875_);
                                        lean_dec_ref(v_arg_2871_);
                                        v___x_2885_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_2854_, v_x_2853_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
                                        return v___x_2885_;
                                    } else {
                                        v___x_2886_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2883_);
                                        v___x_2887_ = l_Lean_Expr_isApp(v___x_2886_);
                                        if v___x_2887_ == 0 {
                                            lean_dec_ref(v___x_2886_);
                                            lean_dec_ref(v_arg_2879_);
                                            lean_dec_ref(v_arg_2875_);
                                            lean_dec_ref(v_arg_2871_);
                                            v___x_2888_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_2854_, v_x_2853_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
                                            return v___x_2888_;
                                        } else {
                                            v___x_2889_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2886_);
                                            v___x_2890_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11;
                                            v___x_2891_ =
                                                l_Lean_Expr_isConstOf(v___x_2889_, v___x_2890_);
                                            lean_dec_ref(v___x_2889_);
                                            if v___x_2891_ == 0 {
                                                lean_dec_ref(v_arg_2879_);
                                                lean_dec_ref(v_arg_2875_);
                                                lean_dec_ref(v_arg_2871_);
                                                v___x_2892_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_2854_, v_x_2853_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
                                                return v___x_2892_;
                                            } else {
                                                v___x_2893_ =
                                                    l_Lean_Meta_Structural_isInstHMulInt___redArg(
                                                        v_arg_2879_,
                                                        v_a_2862_,
                                                    );
                                                if lean_obj_tag(v___x_2893_) == 0 {
                                                    v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
                                                    lean_inc(v_a_2894_);
                                                    lean_dec_ref_known(v___x_2893_, 1);
                                                    v___x_2895_ = (lean_unbox(v_a_2894_) as u8);
                                                    lean_dec(v_a_2894_);
                                                    if v___x_2895_ == 0 {
                                                        lean_dec_ref(v_arg_2875_);
                                                        lean_dec_ref(v_arg_2871_);
                                                        v___x_2896_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_2854_, v_x_2853_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
                                                        return v___x_2896_;
                                                    } else {
                                                        lean_dec_ref(v_e_2854_);
                                                        lean_inc(v_x_2853_);
                                                        v___x_2897_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_2853_, v_arg_2875_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
                                                        if lean_obj_tag(v___x_2897_) == 0 {
                                                            lean_dec_ref_known(v___x_2897_, 1);
                                                            v_e_2854_ = v_arg_2871_;
                                                            state = 0;
                                                            continue;
                                                        } else {
                                                            lean_dec_ref(v_arg_2871_);
                                                            lean_dec(v_x_2853_);
                                                            return v___x_2897_;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v_arg_2875_);
                                                    lean_dec_ref(v_arg_2871_);
                                                    lean_dec_ref(v_e_2854_);
                                                    lean_dec(v_x_2853_);
                                                    v_a_2899_ = lean_ctor_get(v___x_2893_, 0);
                                                    v_isSharedCheck_2906_ =
                                                        (!lean_is_exclusive(v___x_2893_)) as u8;
                                                    if v_isSharedCheck_2906_ == 0 {
                                                        v___x_2901_ = v___x_2893_;
                                                        v_isShared_2902_ = v_isSharedCheck_2906_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2899_);
                                                        lean_dec(v___x_2893_);
                                                        v___x_2901_ = lean_box(0);
                                                        v_isShared_2902_ = v_isSharedCheck_2906_;
                                                        state = 1;
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
                } else {
                    lean_dec_ref(v_e_2854_);
                    lean_dec(v_x_2853_);
                    v_a_2907_ = lean_ctor_get(v___x_2866_, 0);
                    v_isSharedCheck_2914_ = (!lean_is_exclusive(v___x_2866_)) as u8;
                    if v_isSharedCheck_2914_ == 0 {
                        v___x_2909_ = v___x_2866_;
                        v_isShared_2910_ = v_isSharedCheck_2914_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2907_);
                        lean_dec(v___x_2866_);
                        v___x_2909_ = lean_box(0);
                        v_isShared_2910_ = v_isSharedCheck_2914_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2902_ == 0 {
                    v___x_2904_ = v___x_2901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
                    v___x_2904_ = v_reuseFailAlloc_2905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2904_;
            }
            3 => {
                if v_isShared_2910_ == 0 {
                    v___x_2912_ = v___x_2909_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
                    v___x_2912_ = v_reuseFailAlloc_2913_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go___boxed(
    mut v_x_2915_: *mut LeanObject,
    mut v_e_2916_: *mut LeanObject,
    mut v_a_2917_: *mut LeanObject,
    mut v_a_2918_: *mut LeanObject,
    mut v_a_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
    mut v_a_2922_: *mut LeanObject,
    mut v_a_2923_: *mut LeanObject,
    mut v_a_2924_: *mut LeanObject,
    mut v_a_2925_: *mut LeanObject,
    mut v_a_2926_: *mut LeanObject,
    mut v_a_2927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2928_: *mut LeanObject = core::ptr::null_mut();
    v_res_2928_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_2915_, v_e_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
    lean_dec(v_a_2926_);
    lean_dec_ref(v_a_2925_);
    lean_dec(v_a_2924_);
    lean_dec_ref(v_a_2923_);
    lean_dec(v_a_2922_);
    lean_dec_ref(v_a_2921_);
    lean_dec(v_a_2920_);
    lean_dec_ref(v_a_2919_);
    lean_dec(v_a_2918_);
    lean_dec(v_a_2917_);
    return v_res_2928_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(
    mut v_e_2929_: *mut LeanObject,
    mut v_x_2930_: *mut LeanObject,
    mut v_a_2931_: *mut LeanObject,
    mut v_a_2932_: *mut LeanObject,
    mut v_a_2933_: *mut LeanObject,
    mut v_a_2934_: *mut LeanObject,
    mut v_a_2935_: *mut LeanObject,
    mut v_a_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
    mut v_a_2939_: *mut LeanObject,
    mut v_a_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v_arg_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    let mut v_arg_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: u8 = 0;
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: u8 = 0;
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___y_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_a_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3010_: u8 = 0;
    let mut v_a_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3014_: u8 = 0;
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut v_a_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3022_: u8 = 0;
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3026_: u8 = 0;
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: u8 = 0;
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: u8 = 0;
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3043_: u8 = 0;
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v_a_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3052_: u8 = 0;
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2945_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2929_, v_a_2938_);
                if lean_obj_tag(v___x_2945_) == 0 {
                    v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
                    v_isSharedCheck_3048_ = (!lean_is_exclusive(v___x_2945_)) as u8;
                    if v_isSharedCheck_3048_ == 0 {
                        v___x_2948_ = v___x_2945_;
                        v_isShared_2949_ = v_isSharedCheck_3048_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2946_);
                        lean_dec(v___x_2945_);
                        v___x_2948_ = lean_box(0);
                        v_isShared_2949_ = v_isSharedCheck_3048_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_x_2930_);
                    v_a_3049_ = lean_ctor_get(v___x_2945_, 0);
                    v_isSharedCheck_3056_ = (!lean_is_exclusive(v___x_2945_)) as u8;
                    if v_isSharedCheck_3056_ == 0 {
                        v___x_3051_ = v___x_2945_;
                        v_isShared_3052_ = v_isSharedCheck_3056_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_3049_);
                        lean_dec(v___x_2945_);
                        v___x_3051_ = lean_box(0);
                        v_isShared_3052_ = v_isSharedCheck_3056_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2943_ = lean_box(0);
                v___x_2944_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2944_, 0, v___x_2943_);
                return v___x_2944_;
            }
            2 => {
                v___x_2955_ = l_Lean_Expr_cleanupAnnotations(v_a_2946_);
                v___x_2956_ = l_Lean_Expr_isApp(v___x_2955_);
                if v___x_2956_ == 0 {
                    lean_dec_ref(v___x_2955_);
                    lean_dec(v_x_2930_);
                    state = 3;
                    continue;
                } else {
                    v_arg_2957_ = lean_ctor_get(v___x_2955_, 1);
                    lean_inc_ref(v_arg_2957_);
                    v___x_2958_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2955_);
                    v___x_2959_ = l_Lean_Expr_isApp(v___x_2958_);
                    if v___x_2959_ == 0 {
                        lean_dec_ref(v___x_2958_);
                        lean_dec_ref(v_arg_2957_);
                        lean_dec(v_x_2930_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_2960_ = lean_ctor_get(v___x_2958_, 1);
                        lean_inc_ref(v_arg_2960_);
                        v___x_2961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2958_);
                        v___x_2962_ = l_Lean_Expr_isApp(v___x_2961_);
                        if v___x_2962_ == 0 {
                            lean_dec_ref(v___x_2961_);
                            lean_dec_ref(v_arg_2960_);
                            lean_dec_ref(v_arg_2957_);
                            lean_dec(v_x_2930_);
                            state = 3;
                            continue;
                        } else {
                            v___x_2963_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2961_);
                            v___x_2964_ = l_Lean_Expr_isApp(v___x_2963_);
                            if v___x_2964_ == 0 {
                                lean_dec_ref(v___x_2963_);
                                lean_dec_ref(v_arg_2960_);
                                lean_dec_ref(v_arg_2957_);
                                lean_dec(v_x_2930_);
                                state = 3;
                                continue;
                            } else {
                                v___x_2965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2963_);
                                v___x_2966_ = l_Lean_Expr_isApp(v___x_2965_);
                                if v___x_2966_ == 0 {
                                    lean_dec_ref(v___x_2965_);
                                    lean_dec_ref(v_arg_2960_);
                                    lean_dec_ref(v_arg_2957_);
                                    lean_dec(v_x_2930_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_2967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2965_);
                                    v___x_2968_ = l_Lean_Expr_isApp(v___x_2967_);
                                    if v___x_2968_ == 0 {
                                        lean_dec_ref(v___x_2967_);
                                        lean_dec_ref(v_arg_2960_);
                                        lean_dec_ref(v_arg_2957_);
                                        lean_dec(v_x_2930_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_2969_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2967_);
                                        v___x_2970_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2;
                                        v___x_2971_ =
                                            l_Lean_Expr_isConstOf(v___x_2969_, v___x_2970_);
                                        if v___x_2971_ == 0 {
                                            v___x_3027_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5;
                                            v___x_3028_ =
                                                l_Lean_Expr_isConstOf(v___x_2969_, v___x_3027_);
                                            if v___x_3028_ == 0 {
                                                v___x_3029_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8;
                                                v___x_3030_ =
                                                    l_Lean_Expr_isConstOf(v___x_2969_, v___x_3029_);
                                                if v___x_3030_ == 0 {
                                                    v___x_3031_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11;
                                                    v___x_3032_ = l_Lean_Expr_isConstOf(
                                                        v___x_2969_,
                                                        v___x_3031_,
                                                    );
                                                    lean_dec_ref(v___x_2969_);
                                                    if v___x_3032_ == 0 {
                                                        lean_dec_ref(v_arg_2960_);
                                                        lean_dec_ref(v_arg_2957_);
                                                        lean_dec(v_x_2930_);
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        lean_del_object(v___x_2948_);
                                                        lean_inc(v_x_2930_);
                                                        v___x_3033_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_2930_, v_arg_2960_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
                                                        if lean_obj_tag(v___x_3033_) == 0 {
                                                            lean_dec_ref_known(v___x_3033_, 1);
                                                            v___x_3034_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_2930_, v_arg_2957_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
                                                            return v___x_3034_;
                                                        } else {
                                                            lean_dec_ref(v_arg_2957_);
                                                            lean_dec(v_x_2930_);
                                                            return v___x_3033_;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_2969_);
                                                    lean_dec_ref(v_arg_2960_);
                                                    lean_del_object(v___x_2948_);
                                                    v___x_3035_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_2957_, v_x_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
                                                    return v___x_3035_;
                                                }
                                            } else {
                                                lean_dec_ref(v___x_2969_);
                                                lean_dec_ref(v_arg_2960_);
                                                lean_del_object(v___x_2948_);
                                                v___x_3036_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_2957_, v_x_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
                                                return v___x_3036_;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_2969_);
                                            lean_del_object(v___x_2948_);
                                            lean_inc_ref(v_arg_2960_);
                                            v___x_3037_ = l_Lean_Meta_getIntValue_x3f(
                                                v_arg_2960_,
                                                v_a_2937_,
                                                v_a_2938_,
                                                v_a_2939_,
                                                v_a_2940_,
                                            );
                                            if lean_obj_tag(v___x_3037_) == 0 {
                                                v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
                                                lean_inc(v_a_3038_);
                                                lean_dec_ref_known(v___x_3037_, 1);
                                                if lean_obj_tag(v_a_3038_) == 0 {
                                                    if v___x_2971_ == 0 {
                                                        lean_dec_ref(v_arg_2960_);
                                                        v___y_2973_ = v_a_2931_;
                                                        v___y_2974_ = v_a_2932_;
                                                        v___y_2975_ = v_a_2933_;
                                                        v___y_2976_ = v_a_2934_;
                                                        v___y_2977_ = v_a_2935_;
                                                        v___y_2978_ = v_a_2936_;
                                                        v___y_2979_ = v_a_2937_;
                                                        v___y_2980_ = v_a_2938_;
                                                        v___y_2981_ = v_a_2939_;
                                                        v___y_2982_ = v_a_2940_;
                                                        state = 5;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_x_2930_);
                                                        v___x_3039_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_2960_, v_x_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
                                                        if lean_obj_tag(v___x_3039_) == 0 {
                                                            lean_dec_ref_known(v___x_3039_, 1);
                                                            v___y_2973_ = v_a_2931_;
                                                            v___y_2974_ = v_a_2932_;
                                                            v___y_2975_ = v_a_2933_;
                                                            v___y_2976_ = v_a_2934_;
                                                            v___y_2977_ = v_a_2935_;
                                                            v___y_2978_ = v_a_2936_;
                                                            v___y_2979_ = v_a_2937_;
                                                            v___y_2980_ = v_a_2938_;
                                                            v___y_2981_ = v_a_2939_;
                                                            v___y_2982_ = v_a_2940_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            lean_dec_ref(v_arg_2957_);
                                                            lean_dec(v_x_2930_);
                                                            return v___x_3039_;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref_known(v_a_3038_, 1);
                                                    lean_dec_ref(v_arg_2960_);
                                                    v___y_2973_ = v_a_2931_;
                                                    v___y_2974_ = v_a_2932_;
                                                    v___y_2975_ = v_a_2933_;
                                                    v___y_2976_ = v_a_2934_;
                                                    v___y_2977_ = v_a_2935_;
                                                    v___y_2978_ = v_a_2936_;
                                                    v___y_2979_ = v_a_2937_;
                                                    v___y_2980_ = v_a_2938_;
                                                    v___y_2981_ = v_a_2939_;
                                                    v___y_2982_ = v_a_2940_;
                                                    state = 5;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_2960_);
                                                lean_dec_ref(v_arg_2957_);
                                                lean_dec(v_x_2930_);
                                                v_a_3040_ = lean_ctor_get(v___x_3037_, 0);
                                                v_isSharedCheck_3047_ =
                                                    (!lean_is_exclusive(v___x_3037_)) as u8;
                                                if v_isSharedCheck_3047_ == 0 {
                                                    v___x_3042_ = v___x_3037_;
                                                    v_isShared_3043_ = v_isSharedCheck_3047_;
                                                    state = 14;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3040_);
                                                    lean_dec(v___x_3037_);
                                                    v___x_3042_ = lean_box(0);
                                                    v_isShared_3043_ = v_isSharedCheck_3047_;
                                                    state = 14;
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
            3 => {
                v___x_2951_ = lean_box(0);
                if v_isShared_2949_ == 0 {
                    lean_ctor_set(v___x_2948_, 0, v___x_2951_);
                    v___x_2953_ = v___x_2948_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
                    v___x_2953_ = v_reuseFailAlloc_2954_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2953_;
            }
            5 => {
                lean_inc_ref(v_arg_2957_);
                v___x_2983_ = l_Lean_Meta_getIntValue_x3f(
                    v_arg_2957_,
                    v___y_2979_,
                    v___y_2980_,
                    v___y_2981_,
                    v___y_2982_,
                );
                if lean_obj_tag(v___x_2983_) == 0 {
                    v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
                    lean_inc(v_a_2984_);
                    lean_dec_ref_known(v___x_2983_, 1);
                    v___x_2985_ = l_Lean_Meta_getNatValue_x3f(
                        v_arg_2957_,
                        v___y_2979_,
                        v___y_2980_,
                        v___y_2981_,
                        v___y_2982_,
                    );
                    if lean_obj_tag(v___x_2985_) == 0 {
                        if lean_obj_tag(v_a_2984_) == 0 {
                            if v___x_2971_ == 0 {
                                lean_dec_ref_known(v___x_2985_, 1);
                                lean_dec_ref(v_arg_2957_);
                                lean_dec(v_x_2930_);
                                state = 1;
                                continue;
                            } else {
                                v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
                                lean_inc(v_a_2986_);
                                lean_dec_ref_known(v___x_2985_, 1);
                                if lean_obj_tag(v_a_2986_) == 0 {
                                    lean_inc_ref(v_arg_2957_);
                                    v___x_2987_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
                                        v_arg_2957_,
                                        v___y_2973_,
                                        v___y_2974_,
                                        v___y_2975_,
                                        v___y_2976_,
                                        v___y_2977_,
                                        v___y_2978_,
                                        v___y_2979_,
                                        v___y_2980_,
                                        v___y_2981_,
                                        v___y_2982_,
                                    );
                                    if lean_obj_tag(v___x_2987_) == 0 {
                                        v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
                                        lean_inc(v_a_2988_);
                                        lean_dec_ref_known(v___x_2987_, 1);
                                        v_fst_2989_ = lean_ctor_get(v_a_2988_, 0);
                                        lean_inc(v_fst_2989_);
                                        lean_dec(v_a_2988_);
                                        v___x_2990_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                            v_arg_2957_,
                                            v___y_2973_,
                                        );
                                        lean_dec_ref(v_arg_2957_);
                                        if lean_obj_tag(v___x_2990_) == 0 {
                                            v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
                                            lean_inc(v_a_2991_);
                                            lean_dec_ref_known(v___x_2990_, 1);
                                            v___x_2992_ = lean_box(0);
                                            lean_inc(v___y_2982_);
                                            lean_inc_ref(v___y_2981_);
                                            lean_inc(v___y_2980_);
                                            lean_inc_ref(v___y_2979_);
                                            lean_inc(v___y_2978_);
                                            lean_inc_ref(v___y_2977_);
                                            lean_inc(v___y_2976_);
                                            lean_inc_ref(v___y_2975_);
                                            lean_inc(v___y_2974_);
                                            lean_inc(v___y_2973_);
                                            lean_inc(v_fst_2989_);
                                            v___x_2993_ = lean_grind_internalize(
                                                v_fst_2989_,
                                                v_a_2991_,
                                                v___x_2992_,
                                                v___y_2973_,
                                                v___y_2974_,
                                                v___y_2975_,
                                                v___y_2976_,
                                                v___y_2977_,
                                                v___y_2978_,
                                                v___y_2979_,
                                                v___y_2980_,
                                                v___y_2981_,
                                                v___y_2982_,
                                            );
                                            if lean_obj_tag(v___x_2993_) == 0 {
                                                lean_dec_ref_known(v___x_2993_, 1);
                                                v___x_2994_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_fst_2989_, v_x_2930_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
                                                return v___x_2994_;
                                            } else {
                                                lean_dec(v_fst_2989_);
                                                lean_dec(v_x_2930_);
                                                return v___x_2993_;
                                            }
                                        } else {
                                            lean_dec(v_fst_2989_);
                                            lean_dec(v_x_2930_);
                                            v_a_2995_ = lean_ctor_get(v___x_2990_, 0);
                                            v_isSharedCheck_3002_ =
                                                (!lean_is_exclusive(v___x_2990_)) as u8;
                                            if v_isSharedCheck_3002_ == 0 {
                                                v___x_2997_ = v___x_2990_;
                                                v_isShared_2998_ = v_isSharedCheck_3002_;
                                                state = 6;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2995_);
                                                lean_dec(v___x_2990_);
                                                v___x_2997_ = lean_box(0);
                                                v_isShared_2998_ = v_isSharedCheck_3002_;
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_arg_2957_);
                                        lean_dec(v_x_2930_);
                                        v_a_3003_ = lean_ctor_get(v___x_2987_, 0);
                                        v_isSharedCheck_3010_ =
                                            (!lean_is_exclusive(v___x_2987_)) as u8;
                                        if v_isSharedCheck_3010_ == 0 {
                                            v___x_3005_ = v___x_2987_;
                                            v_isShared_3006_ = v_isSharedCheck_3010_;
                                            state = 8;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3003_);
                                            lean_dec(v___x_2987_);
                                            v___x_3005_ = lean_box(0);
                                            v_isShared_3006_ = v_isSharedCheck_3010_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v_a_2986_, 1);
                                    lean_dec_ref(v_arg_2957_);
                                    lean_dec(v_x_2930_);
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_a_2984_, 1);
                            lean_dec_ref_known(v___x_2985_, 1);
                            lean_dec_ref(v_arg_2957_);
                            lean_dec(v_x_2930_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2984_);
                        lean_dec_ref(v_arg_2957_);
                        lean_dec(v_x_2930_);
                        v_a_3011_ = lean_ctor_get(v___x_2985_, 0);
                        v_isSharedCheck_3018_ = (!lean_is_exclusive(v___x_2985_)) as u8;
                        if v_isSharedCheck_3018_ == 0 {
                            v___x_3013_ = v___x_2985_;
                            v_isShared_3014_ = v_isSharedCheck_3018_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3011_);
                            lean_dec(v___x_2985_);
                            v___x_3013_ = lean_box(0);
                            v_isShared_3014_ = v_isSharedCheck_3018_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_arg_2957_);
                    lean_dec(v_x_2930_);
                    v_a_3019_ = lean_ctor_get(v___x_2983_, 0);
                    v_isSharedCheck_3026_ = (!lean_is_exclusive(v___x_2983_)) as u8;
                    if v_isSharedCheck_3026_ == 0 {
                        v___x_3021_ = v___x_2983_;
                        v_isShared_3022_ = v_isSharedCheck_3026_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3019_);
                        lean_dec(v___x_2983_);
                        v___x_3021_ = lean_box(0);
                        v_isShared_3022_ = v_isSharedCheck_3026_;
                        state = 12;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_2998_ == 0 {
                    v___x_3000_ = v___x_2997_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
                    v___x_3000_ = v_reuseFailAlloc_3001_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3000_;
            }
            8 => {
                if v_isShared_3006_ == 0 {
                    v___x_3008_ = v___x_3005_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
                    v___x_3008_ = v_reuseFailAlloc_3009_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3008_;
            }
            10 => {
                if v_isShared_3014_ == 0 {
                    v___x_3016_ = v___x_3013_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
                    v___x_3016_ = v_reuseFailAlloc_3017_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3016_;
            }
            12 => {
                if v_isShared_3022_ == 0 {
                    v___x_3024_ = v___x_3021_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
                    v___x_3024_ = v_reuseFailAlloc_3025_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3024_;
            }
            14 => {
                if v_isShared_3043_ == 0 {
                    v___x_3045_ = v___x_3042_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
                    v___x_3045_ = v_reuseFailAlloc_3046_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3045_;
            }
            16 => {
                if v_isShared_3052_ == 0 {
                    v___x_3054_ = v___x_3051_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
                    v___x_3054_ = v_reuseFailAlloc_3055_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(
    mut v_e_3057_: *mut LeanObject,
    mut v_x_3058_: *mut LeanObject,
    mut v_a_3059_: *mut LeanObject,
    mut v_a_3060_: *mut LeanObject,
    mut v_a_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
    mut v_a_3065_: *mut LeanObject,
    mut v_a_3066_: *mut LeanObject,
    mut v_a_3067_: *mut LeanObject,
    mut v_a_3068_: *mut LeanObject,
    mut v_a_3069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3070_: *mut LeanObject = core::ptr::null_mut();
    v_res_3070_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_3057_, v_x_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
    lean_dec(v_a_3068_);
    lean_dec_ref(v_a_3067_);
    lean_dec(v_a_3066_);
    lean_dec_ref(v_a_3065_);
    lean_dec(v_a_3064_);
    lean_dec_ref(v_a_3063_);
    lean_dec(v_a_3062_);
    lean_dec_ref(v_a_3061_);
    lean_dec(v_a_3060_);
    lean_dec(v_a_3059_);
    return v_res_3070_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(
    mut v_x_3071_: *mut LeanObject,
    mut v_x_3072_: *mut LeanObject,
    mut v_x_3073_: *mut LeanObject,
    mut v_x_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: u8 = 0;
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: u8 = 0;
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3100_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3075_ = lean_ctor_get(v_x_3071_, 0);
                v_vs_3076_ = lean_ctor_get(v_x_3071_, 1);
                v_isSharedCheck_3100_ = (!lean_is_exclusive(v_x_3071_)) as u8;
                if v_isSharedCheck_3100_ == 0 {
                    v___x_3078_ = v_x_3071_;
                    v_isShared_3079_ = v_isSharedCheck_3100_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3076_);
                    lean_inc(v_ks_3075_);
                    lean_dec(v_x_3071_);
                    v___x_3078_ = lean_box(0);
                    v_isShared_3079_ = v_isSharedCheck_3100_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3080_ = lean_array_get_size(v_ks_3075_);
                v___x_3081_ = lean_nat_dec_lt(v_x_3072_, v___x_3080_);
                if v___x_3081_ == 0 {
                    lean_dec(v_x_3072_);
                    v___x_3082_ = lean_array_push(v_ks_3075_, v_x_3073_);
                    v___x_3083_ = lean_array_push(v_vs_3076_, v_x_3074_);
                    if v_isShared_3079_ == 0 {
                        lean_ctor_set(v___x_3078_, 1, v___x_3083_);
                        lean_ctor_set(v___x_3078_, 0, v___x_3082_);
                        v___x_3085_ = v___x_3078_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3082_);
                        lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3083_);
                        v___x_3085_ = v_reuseFailAlloc_3086_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3087_ = lean_array_fget_borrowed(v_ks_3075_, v_x_3072_);
                    v___x_3088_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_3073_,
                            v_k_x27_3087_,
                        );
                    if v___x_3088_ == 0 {
                        if v_isShared_3079_ == 0 {
                            v___x_3090_ = v___x_3078_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_ks_3075_);
                            lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_vs_3076_);
                            v___x_3090_ = v_reuseFailAlloc_3094_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3095_ = lean_array_fset(v_ks_3075_, v_x_3072_, v_x_3073_);
                        v___x_3096_ = lean_array_fset(v_vs_3076_, v_x_3072_, v_x_3074_);
                        lean_dec(v_x_3072_);
                        if v_isShared_3079_ == 0 {
                            lean_ctor_set(v___x_3078_, 1, v___x_3096_);
                            lean_ctor_set(v___x_3078_, 0, v___x_3095_);
                            v___x_3098_ = v___x_3078_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3095_);
                            lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_3096_);
                            v___x_3098_ = v_reuseFailAlloc_3099_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3085_;
            }
            3 => {
                v___x_3091_ = lean_unsigned_to_nat(1);
                v___x_3092_ = lean_nat_add(v_x_3072_, v___x_3091_);
                lean_dec(v_x_3072_);
                v_x_3071_ = v___x_3090_;
                v_x_3072_ = v___x_3092_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3098_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(
    mut v_n_3101_: *mut LeanObject,
    mut v_k_3102_: *mut LeanObject,
    mut v_v_3103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    v___x_3104_ = lean_unsigned_to_nat(0);
    v___x_3105_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_3101_, v___x_3104_, v_k_3102_, v_v_3103_);
    return v___x_3105_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    v___x_3106_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3106_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(
    mut v_x_3107_: *mut LeanObject,
    mut v_x_3108_: usize,
    mut v_x_3109_: usize,
    mut v_x_3110_: *mut LeanObject,
    mut v_x_3111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: usize = 0;
    let mut v___x_3114_: usize = 0;
    let mut v___x_3115_: usize = 0;
    let mut v___x_3116_: usize = 0;
    let mut v_j_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: u8 = 0;
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v_v_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3136_: u8 = 0;
    let mut v___x_3137_: u8 = 0;
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut v_node_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3147_: u8 = 0;
    let mut v___x_3148_: usize = 0;
    let mut v___x_3149_: usize = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3154_: u8 = 0;
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut v_unused_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3162_: u8 = 0;
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3167_: u8 = 0;
    let mut v_ks_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: usize = 0;
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v_reuseFailAlloc_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3107_) == 0 {
                    v_es_3112_ = lean_ctor_get(v_x_3107_, 0);
                    v___x_3113_ = 5usize;
                    v___x_3114_ = 1usize;
                    v___x_3115_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
                    v___x_3116_ = lean_usize_land(v_x_3108_, v___x_3115_);
                    v_j_3117_ = lean_usize_to_nat(v___x_3116_);
                    v___x_3118_ = lean_array_get_size(v_es_3112_);
                    v___x_3119_ = lean_nat_dec_lt(v_j_3117_, v___x_3118_);
                    if v___x_3119_ == 0 {
                        lean_dec(v_j_3117_);
                        lean_dec(v_x_3111_);
                        lean_dec_ref(v_x_3110_);
                        return v_x_3107_;
                    } else {
                        lean_inc_ref(v_es_3112_);
                        v_isSharedCheck_3156_ = (!lean_is_exclusive(v_x_3107_)) as u8;
                        if v_isSharedCheck_3156_ == 0 {
                            v_unused_3157_ = lean_ctor_get(v_x_3107_, 0);
                            lean_dec(v_unused_3157_);
                            v___x_3121_ = v_x_3107_;
                            v_isShared_3122_ = v_isSharedCheck_3156_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3107_);
                            v___x_3121_ = lean_box(0);
                            v_isShared_3122_ = v_isSharedCheck_3156_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3158_ = lean_ctor_get(v_x_3107_, 0);
                    v_vs_3159_ = lean_ctor_get(v_x_3107_, 1);
                    v_isSharedCheck_3179_ = (!lean_is_exclusive(v_x_3107_)) as u8;
                    if v_isSharedCheck_3179_ == 0 {
                        v___x_3161_ = v_x_3107_;
                        v_isShared_3162_ = v_isSharedCheck_3179_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3159_);
                        lean_inc(v_ks_3158_);
                        lean_dec(v_x_3107_);
                        v___x_3161_ = lean_box(0);
                        v_isShared_3162_ = v_isSharedCheck_3179_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3123_ = lean_array_fget(v_es_3112_, v_j_3117_);
                v___x_3124_ = lean_box(0);
                v_xs_x27_3125_ = lean_array_fset(v_es_3112_, v_j_3117_, v___x_3124_);
                match lean_obj_tag(v_v_3123_) {
                    0 => {
                        v_key_3132_ = lean_ctor_get(v_v_3123_, 0);
                        v_val_3133_ = lean_ctor_get(v_v_3123_, 1);
                        v_isSharedCheck_3143_ = (!lean_is_exclusive(v_v_3123_)) as u8;
                        if v_isSharedCheck_3143_ == 0 {
                            v___x_3135_ = v_v_3123_;
                            v_isShared_3136_ = v_isSharedCheck_3143_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3133_);
                            lean_inc(v_key_3132_);
                            lean_dec(v_v_3123_);
                            v___x_3135_ = lean_box(0);
                            v_isShared_3136_ = v_isSharedCheck_3143_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3144_ = lean_ctor_get(v_v_3123_, 0);
                        v_isSharedCheck_3154_ = (!lean_is_exclusive(v_v_3123_)) as u8;
                        if v_isSharedCheck_3154_ == 0 {
                            v___x_3146_ = v_v_3123_;
                            v_isShared_3147_ = v_isSharedCheck_3154_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3144_);
                            lean_dec(v_v_3123_);
                            v___x_3146_ = lean_box(0);
                            v_isShared_3147_ = v_isSharedCheck_3154_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3155_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3155_, 0, v_x_3110_);
                        lean_ctor_set(v___x_3155_, 1, v_x_3111_);
                        v___y_3127_ = v___x_3155_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3128_ = lean_array_fset(v_xs_x27_3125_, v_j_3117_, v___y_3127_);
                lean_dec(v_j_3117_);
                if v_isShared_3122_ == 0 {
                    lean_ctor_set(v___x_3121_, 0, v___x_3128_);
                    v___x_3130_ = v___x_3121_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
                    v___x_3130_ = v_reuseFailAlloc_3131_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3130_;
            }
            4 => {
                v___x_3137_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_3110_,
                        v_key_3132_,
                    );
                if v___x_3137_ == 0 {
                    lean_del_object(v___x_3135_);
                    v___x_3138_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3132_,
                        v_val_3133_,
                        v_x_3110_,
                        v_x_3111_,
                    );
                    v___x_3139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3139_, 0, v___x_3138_);
                    v___y_3127_ = v___x_3139_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3133_);
                    lean_dec(v_key_3132_);
                    if v_isShared_3136_ == 0 {
                        lean_ctor_set(v___x_3135_, 1, v_x_3111_);
                        lean_ctor_set(v___x_3135_, 0, v_x_3110_);
                        v___x_3141_ = v___x_3135_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_x_3110_);
                        lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_x_3111_);
                        v___x_3141_ = v_reuseFailAlloc_3142_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3127_ = v___x_3141_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3148_ = lean_usize_shift_right(v_x_3108_, v___x_3113_);
                v___x_3149_ = lean_usize_add(v_x_3109_, v___x_3114_);
                v___x_3150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_3144_, v___x_3148_, v___x_3149_, v_x_3110_, v_x_3111_);
                if v_isShared_3147_ == 0 {
                    lean_ctor_set(v___x_3146_, 0, v___x_3150_);
                    v___x_3152_ = v___x_3146_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
                    v___x_3152_ = v_reuseFailAlloc_3153_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3127_ = v___x_3152_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3162_ == 0 {
                    v___x_3164_ = v___x_3161_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_ks_3158_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_vs_3159_);
                    v___x_3164_ = v_reuseFailAlloc_3178_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3165_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_3164_, v_x_3110_, v_x_3111_);
                v___x_3173_ = 7usize;
                v___x_3174_ = lean_usize_dec_le(v___x_3173_, v_x_3109_);
                if v___x_3174_ == 0 {
                    v___x_3175_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3165_);
                    v___x_3176_ = lean_unsigned_to_nat(4);
                    v___x_3177_ = lean_nat_dec_lt(v___x_3175_, v___x_3176_);
                    lean_dec(v___x_3175_);
                    v___y_3167_ = v___x_3177_;
                    state = 10;
                    continue;
                } else {
                    v___y_3167_ = v___x_3174_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3167_ == 0 {
                    v_ks_3168_ = lean_ctor_get(v_newNode_3165_, 0);
                    lean_inc_ref(v_ks_3168_);
                    v_vs_3169_ = lean_ctor_get(v_newNode_3165_, 1);
                    lean_inc_ref(v_vs_3169_);
                    lean_dec_ref(v_newNode_3165_);
                    v___x_3170_ = lean_unsigned_to_nat(0);
                    v___x_3171_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0);
                    v___x_3172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_3109_, v_ks_3168_, v_vs_3169_, v___x_3170_, v___x_3171_);
                    lean_dec_ref(v_vs_3169_);
                    lean_dec_ref(v_ks_3168_);
                    return v___x_3172_;
                } else {
                    return v_newNode_3165_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(
    mut v_depth_3180_: usize,
    mut v_keys_3181_: *mut LeanObject,
    mut v_vals_3182_: *mut LeanObject,
    mut v_i_3183_: *mut LeanObject,
    mut v_entries_3184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v_k_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u64 = 0;
    let mut v_h_3190_: usize = 0;
    let mut v___x_3191_: usize = 0;
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: usize = 0;
    let mut v___x_3194_: usize = 0;
    let mut v___x_3195_: usize = 0;
    let mut v_h_3196_: usize = 0;
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3185_ = lean_array_get_size(v_keys_3181_);
                v___x_3186_ = lean_nat_dec_lt(v_i_3183_, v___x_3185_);
                if v___x_3186_ == 0 {
                    lean_dec(v_i_3183_);
                    return v_entries_3184_;
                } else {
                    v_k_3187_ = lean_array_fget_borrowed(v_keys_3181_, v_i_3183_);
                    v_v_3188_ = lean_array_fget_borrowed(v_vals_3182_, v_i_3183_);
                    v___x_3189_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_3187_);
                    v_h_3190_ = lean_uint64_to_usize(v___x_3189_);
                    v___x_3191_ = 5usize;
                    v___x_3192_ = lean_unsigned_to_nat(1);
                    v___x_3193_ = 1usize;
                    v___x_3194_ = lean_usize_sub(v_depth_3180_, v___x_3193_);
                    v___x_3195_ = lean_usize_mul(v___x_3191_, v___x_3194_);
                    v_h_3196_ = lean_usize_shift_right(v_h_3190_, v___x_3195_);
                    v___x_3197_ = lean_nat_add(v_i_3183_, v___x_3192_);
                    lean_dec(v_i_3183_);
                    lean_inc(v_v_3188_);
                    lean_inc(v_k_3187_);
                    v___x_3198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_3184_, v_h_3196_, v_depth_3180_, v_k_3187_, v_v_3188_);
                    v_i_3183_ = v___x_3197_;
                    v_entries_3184_ = v___x_3198_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_3200_: *mut LeanObject,
    mut v_keys_3201_: *mut LeanObject,
    mut v_vals_3202_: *mut LeanObject,
    mut v_i_3203_: *mut LeanObject,
    mut v_entries_3204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3205_: usize = 0;
    let mut v_res_3206_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3205_ = lean_unbox_usize(v_depth_3200_);
    lean_dec(v_depth_3200_);
    v_res_3206_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_boxed_3205_, v_keys_3201_, v_vals_3202_, v_i_3203_, v_entries_3204_);
    lean_dec_ref(v_vals_3202_);
    lean_dec_ref(v_keys_3201_);
    return v_res_3206_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(
    mut v_x_3207_: *mut LeanObject,
    mut v_x_3208_: *mut LeanObject,
    mut v_x_3209_: *mut LeanObject,
    mut v_x_3210_: *mut LeanObject,
    mut v_x_3211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_32824__boxed_3212_: usize = 0;
    let mut v_x_32825__boxed_3213_: usize = 0;
    let mut v_res_3214_: *mut LeanObject = core::ptr::null_mut();
    v_x_32824__boxed_3212_ = lean_unbox_usize(v_x_3208_);
    lean_dec(v_x_3208_);
    v_x_32825__boxed_3213_ = lean_unbox_usize(v_x_3209_);
    lean_dec(v_x_3209_);
    v_res_3214_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_3207_, v_x_32824__boxed_3212_, v_x_32825__boxed_3213_, v_x_3210_, v_x_3211_);
    return v_res_3214_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(
    mut v_x_3215_: *mut LeanObject,
    mut v_x_3216_: *mut LeanObject,
    mut v_x_3217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3218_: u64 = 0;
    let mut v___x_3219_: usize = 0;
    let mut v___x_3220_: usize = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    v___x_3218_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3216_);
    v___x_3219_ = lean_uint64_to_usize(v___x_3218_);
    v___x_3220_ = 1usize;
    v___x_3221_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_3215_, v___x_3219_, v___x_3220_, v_x_3216_, v_x_3217_);
    return v___x_3221_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    v___x_3222_ = lean_unsigned_to_nat(32);
    v___x_3223_ = lean_mk_empty_array_with_capacity(v___x_3222_);
    v___x_3224_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3224_, 0, v___x_3223_);
    return v___x_3224_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3225_: usize = 0;
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    v___x_3225_ = 5usize;
    v___x_3226_ = lean_unsigned_to_nat(0);
    v___x_3227_ = lean_unsigned_to_nat(32);
    v___x_3228_ = lean_mk_empty_array_with_capacity(v___x_3227_);
    v___x_3229_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0,
    );
    v___x_3230_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3230_, 0, v___x_3229_);
    lean_ctor_set(v___x_3230_, 1, v___x_3228_);
    lean_ctor_set(v___x_3230_, 2, v___x_3226_);
    lean_ctor_set(v___x_3230_, 3, v___x_3226_);
    lean_ctor_set_usize(v___x_3230_, 4, v___x_3225_);
    return v___x_3230_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(
    mut v_expr_3231_: *mut LeanObject,
    mut v_size_3232_: *mut LeanObject,
    mut v_s_3233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natDef_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dvds_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_3249_: u8 = 0;
    let mut v_conflict_x3f_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_divMod_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_3257_: u8 = 0;
    let mut v_nonlinearOccs_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_3234_ = lean_ctor_get(v_s_3233_, 0);
                v_varMap_3235_ = lean_ctor_get(v_s_3233_, 1);
                v_vars_x27_3236_ = lean_ctor_get(v_s_3233_, 2);
                v_varMap_x27_3237_ = lean_ctor_get(v_s_3233_, 3);
                v_natToIntMap_3238_ = lean_ctor_get(v_s_3233_, 4);
                v_natDef_3239_ = lean_ctor_get(v_s_3233_, 5);
                v_dvds_3240_ = lean_ctor_get(v_s_3233_, 6);
                v_lowers_3241_ = lean_ctor_get(v_s_3233_, 7);
                v_uppers_3242_ = lean_ctor_get(v_s_3233_, 8);
                v_diseqs_3243_ = lean_ctor_get(v_s_3233_, 9);
                v_elimEqs_3244_ = lean_ctor_get(v_s_3233_, 10);
                v_elimStack_3245_ = lean_ctor_get(v_s_3233_, 11);
                v_occurs_3246_ = lean_ctor_get(v_s_3233_, 12);
                v_assignment_3247_ = lean_ctor_get(v_s_3233_, 13);
                v_nextCnstrId_3248_ = lean_ctor_get(v_s_3233_, 14);
                v_caseSplits_3249_ = lean_ctor_get_uint8(
                    v_s_3233_,
                    (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_3250_ = lean_ctor_get(v_s_3233_, 15);
                v_diseqSplits_3251_ = lean_ctor_get(v_s_3233_, 16);
                v_divMod_3252_ = lean_ctor_get(v_s_3233_, 17);
                v_toIntIds_3253_ = lean_ctor_get(v_s_3233_, 18);
                v_toIntInfos_3254_ = lean_ctor_get(v_s_3233_, 19);
                v_toIntTermMap_3255_ = lean_ctor_get(v_s_3233_, 20);
                v_toIntVarMap_3256_ = lean_ctor_get(v_s_3233_, 21);
                v_usedCommRing_3257_ = lean_ctor_get_uint8(
                    v_s_3233_,
                    (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_3258_ = lean_ctor_get(v_s_3233_, 22);
                v_isSharedCheck_3276_ = (!lean_is_exclusive(v_s_3233_)) as u8;
                if v_isSharedCheck_3276_ == 0 {
                    v___x_3260_ = v_s_3233_;
                    v_isShared_3261_ = v_isSharedCheck_3276_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nonlinearOccs_3258_);
                    lean_inc(v_toIntVarMap_3256_);
                    lean_inc(v_toIntTermMap_3255_);
                    lean_inc(v_toIntInfos_3254_);
                    lean_inc(v_toIntIds_3253_);
                    lean_inc(v_divMod_3252_);
                    lean_inc(v_diseqSplits_3251_);
                    lean_inc(v_conflict_x3f_3250_);
                    lean_inc(v_nextCnstrId_3248_);
                    lean_inc(v_assignment_3247_);
                    lean_inc(v_occurs_3246_);
                    lean_inc(v_elimStack_3245_);
                    lean_inc(v_elimEqs_3244_);
                    lean_inc(v_diseqs_3243_);
                    lean_inc(v_uppers_3242_);
                    lean_inc(v_lowers_3241_);
                    lean_inc(v_dvds_3240_);
                    lean_inc(v_natDef_3239_);
                    lean_inc(v_natToIntMap_3238_);
                    lean_inc(v_varMap_x27_3237_);
                    lean_inc(v_vars_x27_3236_);
                    lean_inc(v_varMap_3235_);
                    lean_inc(v_vars_3234_);
                    lean_dec(v_s_3233_);
                    v___x_3260_ = lean_box(0);
                    v_isShared_3261_ = v_isSharedCheck_3276_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_expr_3231_);
                v___x_3262_ = l_Lean_PersistentArray_push___redArg(v_vars_3234_, v_expr_3231_);
                v___x_3263_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_3235_, v_expr_3231_, v_size_3232_);
                v___x_3264_ = lean_box(0);
                v___x_3265_ = l_Lean_PersistentArray_push___redArg(v_dvds_3240_, v___x_3264_);
                v___x_3266_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1,
                );
                v___x_3267_ = l_Lean_PersistentArray_push___redArg(v_lowers_3241_, v___x_3266_);
                v___x_3268_ = l_Lean_PersistentArray_push___redArg(v_uppers_3242_, v___x_3266_);
                v___x_3269_ = l_Lean_PersistentArray_push___redArg(v_diseqs_3243_, v___x_3266_);
                v___x_3270_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_3244_, v___x_3264_);
                v___x_3271_ = lean_box(1);
                v___x_3272_ = l_Lean_PersistentArray_push___redArg(v_occurs_3246_, v___x_3271_);
                if v_isShared_3261_ == 0 {
                    lean_ctor_set(v___x_3260_, 12, v___x_3272_);
                    lean_ctor_set(v___x_3260_, 10, v___x_3270_);
                    lean_ctor_set(v___x_3260_, 9, v___x_3269_);
                    lean_ctor_set(v___x_3260_, 8, v___x_3268_);
                    lean_ctor_set(v___x_3260_, 7, v___x_3267_);
                    lean_ctor_set(v___x_3260_, 6, v___x_3265_);
                    lean_ctor_set(v___x_3260_, 1, v___x_3263_);
                    lean_ctor_set(v___x_3260_, 0, v___x_3262_);
                    v___x_3274_ = v___x_3260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 23, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3262_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 1, v___x_3263_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 2, v_vars_x27_3236_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 3, v_varMap_x27_3237_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 4, v_natToIntMap_3238_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 5, v_natDef_3239_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 6, v___x_3265_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 7, v___x_3267_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 8, v___x_3268_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 9, v___x_3269_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 10, v___x_3270_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 11, v_elimStack_3245_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 12, v___x_3272_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 13, v_assignment_3247_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 14, v_nextCnstrId_3248_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 15, v_conflict_x3f_3250_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 16, v_diseqSplits_3251_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 17, v_divMod_3252_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 18, v_toIntIds_3253_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 19, v_toIntInfos_3254_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 20, v_toIntTermMap_3255_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 21, v_toIntVarMap_3256_);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 22, v_nonlinearOccs_3258_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3275_,
                        (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                        v_caseSplits_3249_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3275_,
                        (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_3257_,
                    );
                    v___x_3274_ = v_reuseFailAlloc_3275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3277_: *mut LeanObject,
    mut v_vals_3278_: *mut LeanObject,
    mut v_i_3279_: *mut LeanObject,
    mut v_k_3280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3281_ = lean_array_get_size(v_keys_3277_);
                v___x_3282_ = lean_nat_dec_lt(v_i_3279_, v___x_3281_);
                if v___x_3282_ == 0 {
                    lean_dec(v_i_3279_);
                    v___x_3283_ = lean_box(0);
                    return v___x_3283_;
                } else {
                    v_k_x27_3284_ = lean_array_fget_borrowed(v_keys_3277_, v_i_3279_);
                    v___x_3285_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_3280_,
                            v_k_x27_3284_,
                        );
                    if v___x_3285_ == 0 {
                        v___x_3286_ = lean_unsigned_to_nat(1);
                        v___x_3287_ = lean_nat_add(v_i_3279_, v___x_3286_);
                        lean_dec(v_i_3279_);
                        v_i_3279_ = v___x_3287_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3289_ = lean_array_fget_borrowed(v_vals_3278_, v_i_3279_);
                        lean_dec(v_i_3279_);
                        lean_inc(v___x_3289_);
                        v___x_3290_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3290_, 0, v___x_3289_);
                        return v___x_3290_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3291_: *mut LeanObject,
    mut v_vals_3292_: *mut LeanObject,
    mut v_i_3293_: *mut LeanObject,
    mut v_k_3294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3295_: *mut LeanObject = core::ptr::null_mut();
    v_res_3295_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_3291_, v_vals_3292_, v_i_3293_, v_k_3294_);
    lean_dec_ref(v_k_3294_);
    lean_dec_ref(v_vals_3292_);
    lean_dec_ref(v_keys_3291_);
    return v_res_3295_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(
    mut v_x_3296_: *mut LeanObject,
    mut v_x_3297_: usize,
    mut v_x_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: usize = 0;
    let mut v___x_3302_: usize = 0;
    let mut v___x_3303_: usize = 0;
    let mut v_j_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: u8 = 0;
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: usize = 0;
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3296_) == 0 {
                    v_es_3299_ = lean_ctor_get(v_x_3296_, 0);
                    v___x_3300_ = lean_box(2);
                    v___x_3301_ = 5usize;
                    v___x_3302_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
                    v___x_3303_ = lean_usize_land(v_x_3297_, v___x_3302_);
                    v_j_3304_ = lean_usize_to_nat(v___x_3303_);
                    v___x_3305_ = lean_array_get_borrowed(v___x_3300_, v_es_3299_, v_j_3304_);
                    lean_dec(v_j_3304_);
                    match lean_obj_tag(v___x_3305_) {
                        0 => {
                            v_key_3306_ = lean_ctor_get(v___x_3305_, 0);
                            v_val_3307_ = lean_ctor_get(v___x_3305_, 1);
                            v___x_3308_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3298_, v_key_3306_);
                            if v___x_3308_ == 0 {
                                v___x_3309_ = lean_box(0);
                                return v___x_3309_;
                            } else {
                                lean_inc(v_val_3307_);
                                v___x_3310_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3310_, 0, v_val_3307_);
                                return v___x_3310_;
                            }
                        }
                        1 => {
                            v_node_3311_ = lean_ctor_get(v___x_3305_, 0);
                            v___x_3312_ = lean_usize_shift_right(v_x_3297_, v___x_3301_);
                            v_x_3296_ = v_node_3311_;
                            v_x_3297_ = v___x_3312_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3314_ = lean_box(0);
                            return v___x_3314_;
                        }
                    }
                } else {
                    v_ks_3315_ = lean_ctor_get(v_x_3296_, 0);
                    v_vs_3316_ = lean_ctor_get(v_x_3296_, 1);
                    v___x_3317_ = lean_unsigned_to_nat(0);
                    v___x_3318_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_3315_, v_vs_3316_, v___x_3317_, v_x_3298_);
                    return v___x_3318_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(
    mut v_x_3319_: *mut LeanObject,
    mut v_x_3320_: *mut LeanObject,
    mut v_x_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33083__boxed_3322_: usize = 0;
    let mut v_res_3323_: *mut LeanObject = core::ptr::null_mut();
    v_x_33083__boxed_3322_ = lean_unbox_usize(v_x_3320_);
    lean_dec(v_x_3320_);
    v_res_3323_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_3319_, v_x_33083__boxed_3322_, v_x_3321_);
    lean_dec_ref(v_x_3321_);
    lean_dec_ref(v_x_3319_);
    return v_res_3323_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(
    mut v_x_3324_: *mut LeanObject,
    mut v_x_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3326_: u64 = 0;
    let mut v___x_3327_: usize = 0;
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    v___x_3326_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3325_);
    v___x_3327_ = lean_uint64_to_usize(v___x_3326_);
    v___x_3328_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_3324_, v___x_3327_, v_x_3325_);
    return v___x_3328_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(
    mut v_x_3329_: *mut LeanObject,
    mut v_x_3330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3331_: *mut LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_3329_, v_x_3330_);
    lean_dec_ref(v_x_3330_);
    lean_dec_ref(v_x_3329_);
    return v_res_3331_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(
    mut v_msgData_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    v___x_3338_ = lean_st_ref_get(v___y_3336_);
    v_env_3339_ = lean_ctor_get(v___x_3338_, 0);
    lean_inc_ref(v_env_3339_);
    lean_dec(v___x_3338_);
    v___x_3340_ = lean_st_ref_get(v___y_3334_);
    v_mctx_3341_ = lean_ctor_get(v___x_3340_, 0);
    lean_inc_ref(v_mctx_3341_);
    lean_dec(v___x_3340_);
    v_lctx_3342_ = lean_ctor_get(v___y_3333_, 2);
    v_options_3343_ = lean_ctor_get(v___y_3335_, 2);
    lean_inc_ref(v_options_3343_);
    lean_inc_ref(v_lctx_3342_);
    v___x_3344_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3344_, 0, v_env_3339_);
    lean_ctor_set(v___x_3344_, 1, v_mctx_3341_);
    lean_ctor_set(v___x_3344_, 2, v_lctx_3342_);
    lean_ctor_set(v___x_3344_, 3, v_options_3343_);
    v___x_3345_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3345_, 0, v___x_3344_);
    lean_ctor_set(v___x_3345_, 1, v_msgData_3332_);
    v___x_3346_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3346_, 0, v___x_3345_);
    return v___x_3346_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(
    mut v_msgData_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3353_: *mut LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
    lean_dec(v___y_3351_);
    lean_dec_ref(v___y_3350_);
    lean_dec(v___y_3349_);
    lean_dec_ref(v___y_3348_);
    return v_res_3353_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: f64 = 0.0;
    v___x_3354_ = lean_unsigned_to_nat(0);
    v___x_3355_ = lean_float_of_nat(v___x_3354_);
    return v___x_3355_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(
    mut v_cls_3359_: *mut LeanObject,
    mut v_msg_3360_: *mut LeanObject,
    mut v___y_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3371_: u8 = 0;
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3384_: u8 = 0;
    let mut v_tid_3385_: u64 = 0;
    let mut v_traces_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: f64 = 0.0;
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3410_: u8 = 0;
    let mut v_isSharedCheck_3411_: u8 = 0;
    let mut v_isSharedCheck_3412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3366_ = lean_ctor_get(v___y_3363_, 5);
                v___x_3367_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msg_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
                v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
                v_isSharedCheck_3412_ = (!lean_is_exclusive(v___x_3367_)) as u8;
                if v_isSharedCheck_3412_ == 0 {
                    v___x_3370_ = v___x_3367_;
                    v_isShared_3371_ = v_isSharedCheck_3412_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3368_);
                    lean_dec(v___x_3367_);
                    v___x_3370_ = lean_box(0);
                    v_isShared_3371_ = v_isSharedCheck_3412_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3372_ = lean_st_ref_take(v___y_3364_);
                v_traceState_3373_ = lean_ctor_get(v___x_3372_, 4);
                v_env_3374_ = lean_ctor_get(v___x_3372_, 0);
                v_nextMacroScope_3375_ = lean_ctor_get(v___x_3372_, 1);
                v_ngen_3376_ = lean_ctor_get(v___x_3372_, 2);
                v_auxDeclNGen_3377_ = lean_ctor_get(v___x_3372_, 3);
                v_cache_3378_ = lean_ctor_get(v___x_3372_, 5);
                v_messages_3379_ = lean_ctor_get(v___x_3372_, 6);
                v_infoState_3380_ = lean_ctor_get(v___x_3372_, 7);
                v_snapshotTasks_3381_ = lean_ctor_get(v___x_3372_, 8);
                v_isSharedCheck_3411_ = (!lean_is_exclusive(v___x_3372_)) as u8;
                if v_isSharedCheck_3411_ == 0 {
                    v___x_3383_ = v___x_3372_;
                    v_isShared_3384_ = v_isSharedCheck_3411_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3381_);
                    lean_inc(v_infoState_3380_);
                    lean_inc(v_messages_3379_);
                    lean_inc(v_cache_3378_);
                    lean_inc(v_traceState_3373_);
                    lean_inc(v_auxDeclNGen_3377_);
                    lean_inc(v_ngen_3376_);
                    lean_inc(v_nextMacroScope_3375_);
                    lean_inc(v_env_3374_);
                    lean_dec(v___x_3372_);
                    v___x_3383_ = lean_box(0);
                    v_isShared_3384_ = v_isSharedCheck_3411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3385_ = lean_ctor_get_uint64(
                    v_traceState_3373_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3386_ = lean_ctor_get(v_traceState_3373_, 0);
                v_isSharedCheck_3410_ = (!lean_is_exclusive(v_traceState_3373_)) as u8;
                if v_isSharedCheck_3410_ == 0 {
                    v___x_3388_ = v_traceState_3373_;
                    v_isShared_3389_ = v_isSharedCheck_3410_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_3386_);
                    lean_dec(v_traceState_3373_);
                    v___x_3388_ = lean_box(0);
                    v_isShared_3389_ = v_isSharedCheck_3410_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3390_ = lean_box(0);
                v___x_3391_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
                v___x_3392_ = 0;
                v___x_3393_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1;
                v___x_3394_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3394_, 0, v_cls_3359_);
                lean_ctor_set(v___x_3394_, 1, v___x_3390_);
                lean_ctor_set(v___x_3394_, 2, v___x_3393_);
                lean_ctor_set_float(
                    v___x_3394_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3391_,
                );
                lean_ctor_set_float(
                    v___x_3394_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3391_,
                );
                lean_ctor_set_uint8(
                    v___x_3394_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3392_,
                );
                v___x_3395_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2;
                v___x_3396_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3396_, 0, v___x_3394_);
                lean_ctor_set(v___x_3396_, 1, v_a_3368_);
                lean_ctor_set(v___x_3396_, 2, v___x_3395_);
                lean_inc(v_ref_3366_);
                v___x_3397_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3397_, 0, v_ref_3366_);
                lean_ctor_set(v___x_3397_, 1, v___x_3396_);
                v___x_3398_ = l_Lean_PersistentArray_push___redArg(v_traces_3386_, v___x_3397_);
                if v_isShared_3389_ == 0 {
                    lean_ctor_set(v___x_3388_, 0, v___x_3398_);
                    v___x_3400_ = v___x_3388_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3398_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3409_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3385_,
                    );
                    v___x_3400_ = v_reuseFailAlloc_3409_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3384_ == 0 {
                    lean_ctor_set(v___x_3383_, 4, v___x_3400_);
                    v___x_3402_ = v___x_3383_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_env_3374_);
                    lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_nextMacroScope_3375_);
                    lean_ctor_set(v_reuseFailAlloc_3408_, 2, v_ngen_3376_);
                    lean_ctor_set(v_reuseFailAlloc_3408_, 3, v_auxDeclNGen_3377_);
                    lean_ctor_set(v_reuseFailAlloc_3408_, 4, v___x_3400_);
                    lean_ctor_set(v_reuseFailAlloc_3408_, 5, v_cache_3378_);
                    lean_ctor_set(v_reuseFailAlloc_3408_, 6, v_messages_3379_);
                    lean_ctor_set(v_reuseFailAlloc_3408_, 7, v_infoState_3380_);
                    lean_ctor_set(v_reuseFailAlloc_3408_, 8, v_snapshotTasks_3381_);
                    v___x_3402_ = v_reuseFailAlloc_3408_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3403_ = lean_st_ref_set(v___y_3364_, v___x_3402_);
                v___x_3404_ = lean_box(0);
                if v_isShared_3371_ == 0 {
                    lean_ctor_set(v___x_3370_, 0, v___x_3404_);
                    v___x_3406_ = v___x_3370_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3404_);
                    v___x_3406_ = v_reuseFailAlloc_3407_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(
    mut v_cls_3413_: *mut LeanObject,
    mut v_msg_3414_: *mut LeanObject,
    mut v___y_3415_: *mut LeanObject,
    mut v___y_3416_: *mut LeanObject,
    mut v___y_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3420_: *mut LeanObject = core::ptr::null_mut();
    v_res_3420_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(
        v_cls_3413_,
        v_msg_3414_,
        v___y_3415_,
        v___y_3416_,
        v___y_3417_,
        v___y_3418_,
    );
    lean_dec(v___y_3418_);
    lean_dec_ref(v___y_3417_);
    lean_dec(v___y_3416_);
    lean_dec_ref(v___y_3415_);
    return v_res_3420_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7() -> *mut LeanObject {
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
    v___x_3434_ = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6;
    v___x_3435_ = l_Lean_Name_append(v___x_3434_, v___x_3433_);
    return v___x_3435_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9() -> *mut LeanObject {
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    v___x_3437_ = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8;
    v___x_3438_ = l_Lean_stringToMessageData(v___x_3437_);
    return v___x_3438_;
}
pub unsafe fn lean_grind_cutsat_mk_var(
    mut v_expr_3439_: *mut LeanObject,
    mut v_a_3440_: *mut LeanObject,
    mut v_a_3441_: *mut LeanObject,
    mut v_a_3442_: *mut LeanObject,
    mut v_a_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
    mut v_a_3445_: *mut LeanObject,
    mut v_a_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
    mut v_a_3448_: *mut LeanObject,
    mut v_a_3449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3455_: u8 = 0;
    let mut v_varMap_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3468_: u8 = 0;
    let mut v___f_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3491_: u8 = 0;
    let mut v___x_3492_: u8 = 0;
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3499_: u8 = 0;
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3503_: u8 = 0;
    let mut v_unused_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3508_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3512_: u8 = 0;
    let mut v_isSharedCheck_3513_: u8 = 0;
    let mut v_a_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3517_: u8 = 0;
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3521_: u8 = 0;
    let mut v_a_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3525_: u8 = 0;
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut v_a_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut v_a_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3545_: u8 = 0;
    let mut v_a_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3549_: u8 = 0;
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3553_: u8 = 0;
    let mut v_a_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3557_: u8 = 0;
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3561_: u8 = 0;
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: u8 = 0;
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v_a_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3584_: u8 = 0;
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3588_: u8 = 0;
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_a_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3593_: u8 = 0;
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3451_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3440_, v_a_3448_);
                if lean_obj_tag(v___x_3451_) == 0 {
                    v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
                    v_isSharedCheck_3589_ = (!lean_is_exclusive(v___x_3451_)) as u8;
                    if v_isSharedCheck_3589_ == 0 {
                        v___x_3454_ = v___x_3451_;
                        v_isShared_3455_ = v_isSharedCheck_3589_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3452_);
                        lean_dec(v___x_3451_);
                        v___x_3454_ = lean_box(0);
                        v_isShared_3455_ = v_isSharedCheck_3589_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3449_);
                    lean_dec_ref(v_a_3448_);
                    lean_dec(v_a_3447_);
                    lean_dec_ref(v_a_3446_);
                    lean_dec(v_a_3445_);
                    lean_dec_ref(v_a_3444_);
                    lean_dec(v_a_3443_);
                    lean_dec_ref(v_a_3442_);
                    lean_dec(v_a_3441_);
                    lean_dec(v_a_3440_);
                    lean_dec_ref(v_expr_3439_);
                    v_a_3590_ = lean_ctor_get(v___x_3451_, 0);
                    v_isSharedCheck_3597_ = (!lean_is_exclusive(v___x_3451_)) as u8;
                    if v_isSharedCheck_3597_ == 0 {
                        v___x_3592_ = v___x_3451_;
                        v_isShared_3593_ = v_isSharedCheck_3597_;
                        state = 26;
                        continue;
                    } else {
                        lean_inc(v_a_3590_);
                        lean_dec(v___x_3451_);
                        v___x_3592_ = lean_box(0);
                        v_isShared_3593_ = v_isSharedCheck_3597_;
                        state = 26;
                        continue;
                    }
                }
            }
            1 => {
                v_varMap_3456_ = lean_ctor_get(v_a_3452_, 1);
                lean_inc_ref(v_varMap_3456_);
                lean_dec(v_a_3452_);
                v___x_3457_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_3456_, v_expr_3439_);
                lean_dec_ref(v_varMap_3456_);
                if lean_obj_tag(v___x_3457_) == 1 {
                    lean_dec(v_a_3449_);
                    lean_dec_ref(v_a_3448_);
                    lean_dec(v_a_3447_);
                    lean_dec_ref(v_a_3446_);
                    lean_dec(v_a_3445_);
                    lean_dec_ref(v_a_3444_);
                    lean_dec(v_a_3443_);
                    lean_dec_ref(v_a_3442_);
                    lean_dec(v_a_3441_);
                    lean_dec(v_a_3440_);
                    lean_dec_ref(v_expr_3439_);
                    v_val_3458_ = lean_ctor_get(v___x_3457_, 0);
                    lean_inc(v_val_3458_);
                    lean_dec_ref_known(v___x_3457_, 1);
                    if v_isShared_3455_ == 0 {
                        lean_ctor_set(v___x_3454_, 0, v_val_3458_);
                        v___x_3460_ = v___x_3454_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_val_3458_);
                        v___x_3460_ = v_reuseFailAlloc_3461_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3457_);
                    lean_del_object(v___x_3454_);
                    v___x_3462_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3440_, v_a_3448_);
                    if lean_obj_tag(v___x_3462_) == 0 {
                        v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
                        lean_inc(v_a_3463_);
                        lean_dec_ref_known(v___x_3462_, 1);
                        v_vars_3464_ = lean_ctor_get(v_a_3463_, 0);
                        lean_inc_ref(v_vars_3464_);
                        lean_dec(v_a_3463_);
                        v_options_3465_ = lean_ctor_get(v_a_3448_, 2);
                        v_size_3466_ = lean_ctor_get(v_vars_3464_, 2);
                        lean_inc_n(v_size_3466_, 2);
                        lean_dec_ref(v_vars_3464_);
                        v_inheritedTraceOptions_3467_ = lean_ctor_get(v_a_3448_, 13);
                        v_hasTrace_3468_ = lean_ctor_get_uint8(
                            v_options_3465_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        lean_inc_ref(v_expr_3439_);
                        v___f_3469_ = lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_3469_, 0, v_expr_3439_);
                        lean_closure_set(v___f_3469_, 1, v_size_3466_);
                        if v_hasTrace_3468_ == 0 {
                            v___y_3471_ = v_a_3440_;
                            v___y_3472_ = v_a_3441_;
                            v___y_3473_ = v_a_3442_;
                            v___y_3474_ = v_a_3443_;
                            v___y_3475_ = v_a_3444_;
                            v___y_3476_ = v_a_3445_;
                            v___y_3477_ = v_a_3446_;
                            v___y_3478_ = v_a_3447_;
                            v___y_3479_ = v_a_3448_;
                            v___y_3480_ = v_a_3449_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3562_ = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
                            v___x_3563_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once
                                ),
                                _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7,
                            );
                            v___x_3564_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3467_,
                                v_options_3465_,
                                v___x_3563_,
                            );
                            if v___x_3564_ == 0 {
                                v___y_3471_ = v_a_3440_;
                                v___y_3472_ = v_a_3441_;
                                v___y_3473_ = v_a_3442_;
                                v___y_3474_ = v_a_3443_;
                                v___y_3475_ = v_a_3444_;
                                v___y_3476_ = v_a_3445_;
                                v___y_3477_ = v_a_3446_;
                                v___y_3478_ = v_a_3447_;
                                v___y_3479_ = v_a_3448_;
                                v___y_3480_ = v_a_3449_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc_ref(v_expr_3439_);
                                v___x_3565_ = l_Lean_MessageData_ofExpr(v_expr_3439_);
                                v___x_3566_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once
                                    ),
                                    _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9,
                                );
                                v___x_3567_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3567_, 0, v___x_3565_);
                                lean_ctor_set(v___x_3567_, 1, v___x_3566_);
                                lean_inc(v_size_3466_);
                                v___x_3568_ = l_Nat_reprFast(v_size_3466_);
                                v___x_3569_ = lean_alloc_ctor(3, 1, (0) as u32);
                                lean_ctor_set(v___x_3569_, 0, v___x_3568_);
                                v___x_3570_ = l_Lean_MessageData_ofFormat(v___x_3569_);
                                v___x_3571_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3571_, 0, v___x_3567_);
                                lean_ctor_set(v___x_3571_, 1, v___x_3570_);
                                v___x_3572_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_3562_, v___x_3571_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
                                if lean_obj_tag(v___x_3572_) == 0 {
                                    lean_dec_ref_known(v___x_3572_, 1);
                                    v___y_3471_ = v_a_3440_;
                                    v___y_3472_ = v_a_3441_;
                                    v___y_3473_ = v_a_3442_;
                                    v___y_3474_ = v_a_3443_;
                                    v___y_3475_ = v_a_3444_;
                                    v___y_3476_ = v_a_3445_;
                                    v___y_3477_ = v_a_3446_;
                                    v___y_3478_ = v_a_3447_;
                                    v___y_3479_ = v_a_3448_;
                                    v___y_3480_ = v_a_3449_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec_ref(v___f_3469_);
                                    lean_dec(v_size_3466_);
                                    lean_dec(v_a_3449_);
                                    lean_dec_ref(v_a_3448_);
                                    lean_dec(v_a_3447_);
                                    lean_dec_ref(v_a_3446_);
                                    lean_dec(v_a_3445_);
                                    lean_dec_ref(v_a_3444_);
                                    lean_dec(v_a_3443_);
                                    lean_dec_ref(v_a_3442_);
                                    lean_dec(v_a_3441_);
                                    lean_dec(v_a_3440_);
                                    lean_dec_ref(v_expr_3439_);
                                    v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
                                    v_isSharedCheck_3580_ = (!lean_is_exclusive(v___x_3572_)) as u8;
                                    if v_isSharedCheck_3580_ == 0 {
                                        v___x_3575_ = v___x_3572_;
                                        v_isShared_3576_ = v_isSharedCheck_3580_;
                                        state = 22;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3573_);
                                        lean_dec(v___x_3572_);
                                        v___x_3575_ = lean_box(0);
                                        v_isShared_3576_ = v_isSharedCheck_3580_;
                                        state = 22;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_3449_);
                        lean_dec_ref(v_a_3448_);
                        lean_dec(v_a_3447_);
                        lean_dec_ref(v_a_3446_);
                        lean_dec(v_a_3445_);
                        lean_dec_ref(v_a_3444_);
                        lean_dec(v_a_3443_);
                        lean_dec_ref(v_a_3442_);
                        lean_dec(v_a_3441_);
                        lean_dec(v_a_3440_);
                        lean_dec_ref(v_expr_3439_);
                        v_a_3581_ = lean_ctor_get(v___x_3462_, 0);
                        v_isSharedCheck_3588_ = (!lean_is_exclusive(v___x_3462_)) as u8;
                        if v_isSharedCheck_3588_ == 0 {
                            v___x_3583_ = v___x_3462_;
                            v_isShared_3584_ = v_isSharedCheck_3588_;
                            state = 24;
                            continue;
                        } else {
                            lean_inc(v_a_3581_);
                            lean_dec(v___x_3462_);
                            v___x_3583_ = lean_box(0);
                            v_isShared_3584_ = v_isSharedCheck_3588_;
                            state = 24;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3460_;
            }
            3 => {
                v___x_3481_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                v___x_3482_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3481_, v___f_3469_, v___y_3471_);
                if lean_obj_tag(v___x_3482_) == 0 {
                    lean_dec_ref_known(v___x_3482_, 1);
                    lean_inc_ref(v_expr_3439_);
                    v___x_3483_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                        v___x_3481_,
                        v_expr_3439_,
                        v___y_3471_,
                        v___y_3472_,
                        v___y_3473_,
                        v___y_3474_,
                        v___y_3475_,
                        v___y_3476_,
                        v___y_3477_,
                        v___y_3478_,
                        v___y_3479_,
                        v___y_3480_,
                    );
                    if lean_obj_tag(v___x_3483_) == 0 {
                        lean_dec_ref_known(v___x_3483_, 1);
                        lean_inc(v_size_3466_);
                        lean_inc_ref(v_expr_3439_);
                        v___x_3484_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(
                            v_expr_3439_,
                            v_size_3466_,
                            v___y_3471_,
                            v___y_3472_,
                            v___y_3473_,
                            v___y_3474_,
                            v___y_3475_,
                            v___y_3476_,
                            v___y_3477_,
                            v___y_3478_,
                            v___y_3479_,
                            v___y_3480_,
                        );
                        if lean_obj_tag(v___x_3484_) == 0 {
                            lean_dec_ref_known(v___x_3484_, 1);
                            lean_inc(v_size_3466_);
                            lean_inc_ref(v_expr_3439_);
                            v___x_3485_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(
                                v_expr_3439_,
                                v_size_3466_,
                                v___y_3471_,
                                v___y_3472_,
                                v___y_3473_,
                                v___y_3474_,
                                v___y_3475_,
                                v___y_3476_,
                                v___y_3477_,
                                v___y_3478_,
                                v___y_3479_,
                                v___y_3480_,
                            );
                            if lean_obj_tag(v___x_3485_) == 0 {
                                lean_dec_ref_known(v___x_3485_, 1);
                                lean_inc(v_size_3466_);
                                lean_inc_ref(v_expr_3439_);
                                v___x_3486_ = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(
                                    v_expr_3439_,
                                    v_size_3466_,
                                    v___y_3471_,
                                    v___y_3472_,
                                    v___y_3473_,
                                    v___y_3474_,
                                    v___y_3475_,
                                    v___y_3476_,
                                    v___y_3477_,
                                    v___y_3478_,
                                    v___y_3479_,
                                    v___y_3480_,
                                );
                                if lean_obj_tag(v___x_3486_) == 0 {
                                    lean_dec_ref_known(v___x_3486_, 1);
                                    lean_inc_ref(v_expr_3439_);
                                    v___x_3487_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_3439_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
                                    if lean_obj_tag(v___x_3487_) == 0 {
                                        v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
                                        v_isSharedCheck_3513_ =
                                            (!lean_is_exclusive(v___x_3487_)) as u8;
                                        if v_isSharedCheck_3513_ == 0 {
                                            v___x_3490_ = v___x_3487_;
                                            v_isShared_3491_ = v_isSharedCheck_3513_;
                                            state = 4;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3488_);
                                            lean_dec(v___x_3487_);
                                            v___x_3490_ = lean_box(0);
                                            v_isShared_3491_ = v_isSharedCheck_3513_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v___y_3480_);
                                        lean_dec_ref(v___y_3479_);
                                        lean_dec(v___y_3478_);
                                        lean_dec_ref(v___y_3477_);
                                        lean_dec(v___y_3476_);
                                        lean_dec_ref(v___y_3475_);
                                        lean_dec(v___y_3474_);
                                        lean_dec_ref(v___y_3473_);
                                        lean_dec(v___y_3472_);
                                        lean_dec(v___y_3471_);
                                        lean_dec(v_size_3466_);
                                        lean_dec_ref(v_expr_3439_);
                                        v_a_3514_ = lean_ctor_get(v___x_3487_, 0);
                                        v_isSharedCheck_3521_ =
                                            (!lean_is_exclusive(v___x_3487_)) as u8;
                                        if v_isSharedCheck_3521_ == 0 {
                                            v___x_3516_ = v___x_3487_;
                                            v_isShared_3517_ = v_isSharedCheck_3521_;
                                            state = 10;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3514_);
                                            lean_dec(v___x_3487_);
                                            v___x_3516_ = lean_box(0);
                                            v_isShared_3517_ = v_isSharedCheck_3521_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v___y_3480_);
                                    lean_dec_ref(v___y_3479_);
                                    lean_dec(v___y_3478_);
                                    lean_dec_ref(v___y_3477_);
                                    lean_dec(v___y_3476_);
                                    lean_dec_ref(v___y_3475_);
                                    lean_dec(v___y_3474_);
                                    lean_dec_ref(v___y_3473_);
                                    lean_dec(v___y_3472_);
                                    lean_dec(v___y_3471_);
                                    lean_dec(v_size_3466_);
                                    lean_dec_ref(v_expr_3439_);
                                    v_a_3522_ = lean_ctor_get(v___x_3486_, 0);
                                    v_isSharedCheck_3529_ = (!lean_is_exclusive(v___x_3486_)) as u8;
                                    if v_isSharedCheck_3529_ == 0 {
                                        v___x_3524_ = v___x_3486_;
                                        v_isShared_3525_ = v_isSharedCheck_3529_;
                                        state = 12;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3522_);
                                        lean_dec(v___x_3486_);
                                        v___x_3524_ = lean_box(0);
                                        v_isShared_3525_ = v_isSharedCheck_3529_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___y_3480_);
                                lean_dec_ref(v___y_3479_);
                                lean_dec(v___y_3478_);
                                lean_dec_ref(v___y_3477_);
                                lean_dec(v___y_3476_);
                                lean_dec_ref(v___y_3475_);
                                lean_dec(v___y_3474_);
                                lean_dec_ref(v___y_3473_);
                                lean_dec(v___y_3472_);
                                lean_dec(v___y_3471_);
                                lean_dec(v_size_3466_);
                                lean_dec_ref(v_expr_3439_);
                                v_a_3530_ = lean_ctor_get(v___x_3485_, 0);
                                v_isSharedCheck_3537_ = (!lean_is_exclusive(v___x_3485_)) as u8;
                                if v_isSharedCheck_3537_ == 0 {
                                    v___x_3532_ = v___x_3485_;
                                    v_isShared_3533_ = v_isSharedCheck_3537_;
                                    state = 14;
                                    continue;
                                } else {
                                    lean_inc(v_a_3530_);
                                    lean_dec(v___x_3485_);
                                    v___x_3532_ = lean_box(0);
                                    v_isShared_3533_ = v_isSharedCheck_3537_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___y_3480_);
                            lean_dec_ref(v___y_3479_);
                            lean_dec(v___y_3478_);
                            lean_dec_ref(v___y_3477_);
                            lean_dec(v___y_3476_);
                            lean_dec_ref(v___y_3475_);
                            lean_dec(v___y_3474_);
                            lean_dec_ref(v___y_3473_);
                            lean_dec(v___y_3472_);
                            lean_dec(v___y_3471_);
                            lean_dec(v_size_3466_);
                            lean_dec_ref(v_expr_3439_);
                            v_a_3538_ = lean_ctor_get(v___x_3484_, 0);
                            v_isSharedCheck_3545_ = (!lean_is_exclusive(v___x_3484_)) as u8;
                            if v_isSharedCheck_3545_ == 0 {
                                v___x_3540_ = v___x_3484_;
                                v_isShared_3541_ = v_isSharedCheck_3545_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_3538_);
                                lean_dec(v___x_3484_);
                                v___x_3540_ = lean_box(0);
                                v_isShared_3541_ = v_isSharedCheck_3545_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_3480_);
                        lean_dec_ref(v___y_3479_);
                        lean_dec(v___y_3478_);
                        lean_dec_ref(v___y_3477_);
                        lean_dec(v___y_3476_);
                        lean_dec_ref(v___y_3475_);
                        lean_dec(v___y_3474_);
                        lean_dec_ref(v___y_3473_);
                        lean_dec(v___y_3472_);
                        lean_dec(v___y_3471_);
                        lean_dec(v_size_3466_);
                        lean_dec_ref(v_expr_3439_);
                        v_a_3546_ = lean_ctor_get(v___x_3483_, 0);
                        v_isSharedCheck_3553_ = (!lean_is_exclusive(v___x_3483_)) as u8;
                        if v_isSharedCheck_3553_ == 0 {
                            v___x_3548_ = v___x_3483_;
                            v_isShared_3549_ = v_isSharedCheck_3553_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_3546_);
                            lean_dec(v___x_3483_);
                            v___x_3548_ = lean_box(0);
                            v_isShared_3549_ = v_isSharedCheck_3553_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_3480_);
                    lean_dec_ref(v___y_3479_);
                    lean_dec(v___y_3478_);
                    lean_dec_ref(v___y_3477_);
                    lean_dec(v___y_3476_);
                    lean_dec_ref(v___y_3475_);
                    lean_dec(v___y_3474_);
                    lean_dec_ref(v___y_3473_);
                    lean_dec(v___y_3472_);
                    lean_dec(v___y_3471_);
                    lean_dec(v_size_3466_);
                    lean_dec_ref(v_expr_3439_);
                    v_a_3554_ = lean_ctor_get(v___x_3482_, 0);
                    v_isSharedCheck_3561_ = (!lean_is_exclusive(v___x_3482_)) as u8;
                    if v_isSharedCheck_3561_ == 0 {
                        v___x_3556_ = v___x_3482_;
                        v_isShared_3557_ = v_isSharedCheck_3561_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_3554_);
                        lean_dec(v___x_3482_);
                        v___x_3556_ = lean_box(0);
                        v_isShared_3557_ = v_isSharedCheck_3561_;
                        state = 20;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3492_ = (lean_unbox(v_a_3488_) as u8);
                lean_dec(v_a_3488_);
                if v___x_3492_ == 0 {
                    lean_dec(v___y_3480_);
                    lean_dec_ref(v___y_3479_);
                    lean_dec(v___y_3478_);
                    lean_dec_ref(v___y_3477_);
                    lean_dec(v___y_3476_);
                    lean_dec_ref(v___y_3475_);
                    lean_dec(v___y_3474_);
                    lean_dec_ref(v___y_3473_);
                    lean_dec(v___y_3472_);
                    lean_dec(v___y_3471_);
                    lean_dec_ref(v_expr_3439_);
                    if v_isShared_3491_ == 0 {
                        lean_ctor_set(v___x_3490_, 0, v_size_3466_);
                        v___x_3494_ = v___x_3490_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_size_3466_);
                        v___x_3494_ = v_reuseFailAlloc_3495_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3490_);
                    lean_inc(v_size_3466_);
                    v___x_3496_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_3439_, v_size_3466_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
                    lean_dec(v___y_3480_);
                    lean_dec_ref(v___y_3479_);
                    lean_dec(v___y_3478_);
                    lean_dec_ref(v___y_3477_);
                    lean_dec(v___y_3476_);
                    lean_dec_ref(v___y_3475_);
                    lean_dec(v___y_3474_);
                    lean_dec_ref(v___y_3473_);
                    lean_dec(v___y_3472_);
                    lean_dec(v___y_3471_);
                    if lean_obj_tag(v___x_3496_) == 0 {
                        v_isSharedCheck_3503_ = (!lean_is_exclusive(v___x_3496_)) as u8;
                        if v_isSharedCheck_3503_ == 0 {
                            v_unused_3504_ = lean_ctor_get(v___x_3496_, 0);
                            lean_dec(v_unused_3504_);
                            v___x_3498_ = v___x_3496_;
                            v_isShared_3499_ = v_isSharedCheck_3503_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v___x_3496_);
                            v___x_3498_ = lean_box(0);
                            v_isShared_3499_ = v_isSharedCheck_3503_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v_size_3466_);
                        v_a_3505_ = lean_ctor_get(v___x_3496_, 0);
                        v_isSharedCheck_3512_ = (!lean_is_exclusive(v___x_3496_)) as u8;
                        if v_isSharedCheck_3512_ == 0 {
                            v___x_3507_ = v___x_3496_;
                            v_isShared_3508_ = v_isSharedCheck_3512_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3505_);
                            lean_dec(v___x_3496_);
                            v___x_3507_ = lean_box(0);
                            v_isShared_3508_ = v_isSharedCheck_3512_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_3494_;
            }
            6 => {
                if v_isShared_3499_ == 0 {
                    lean_ctor_set(v___x_3498_, 0, v_size_3466_);
                    v___x_3501_ = v___x_3498_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_size_3466_);
                    v___x_3501_ = v_reuseFailAlloc_3502_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3501_;
            }
            8 => {
                if v_isShared_3508_ == 0 {
                    v___x_3510_ = v___x_3507_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
                    v___x_3510_ = v_reuseFailAlloc_3511_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3510_;
            }
            10 => {
                if v_isShared_3517_ == 0 {
                    v___x_3519_ = v___x_3516_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
                    v___x_3519_ = v_reuseFailAlloc_3520_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3519_;
            }
            12 => {
                if v_isShared_3525_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
                    v___x_3527_ = v_reuseFailAlloc_3528_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3527_;
            }
            14 => {
                if v_isShared_3533_ == 0 {
                    v___x_3535_ = v___x_3532_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
                    v___x_3535_ = v_reuseFailAlloc_3536_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3535_;
            }
            16 => {
                if v_isShared_3541_ == 0 {
                    v___x_3543_ = v___x_3540_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
                    v___x_3543_ = v_reuseFailAlloc_3544_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3543_;
            }
            18 => {
                if v_isShared_3549_ == 0 {
                    v___x_3551_ = v___x_3548_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
                    v___x_3551_ = v_reuseFailAlloc_3552_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3551_;
            }
            20 => {
                if v_isShared_3557_ == 0 {
                    v___x_3559_ = v___x_3556_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
                    v___x_3559_ = v_reuseFailAlloc_3560_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3559_;
            }
            22 => {
                if v_isShared_3576_ == 0 {
                    v___x_3578_ = v___x_3575_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
                    v___x_3578_ = v_reuseFailAlloc_3579_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3578_;
            }
            24 => {
                if v_isShared_3584_ == 0 {
                    v___x_3586_ = v___x_3583_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
                    v___x_3586_ = v_reuseFailAlloc_3587_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3586_;
            }
            26 => {
                if v_isShared_3593_ == 0 {
                    v___x_3595_ = v___x_3592_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
                    v___x_3595_ = v_reuseFailAlloc_3596_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(
    mut v_expr_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
    mut v_a_3600_: *mut LeanObject,
    mut v_a_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
    mut v_a_3603_: *mut LeanObject,
    mut v_a_3604_: *mut LeanObject,
    mut v_a_3605_: *mut LeanObject,
    mut v_a_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
    mut v_a_3609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3610_: *mut LeanObject = core::ptr::null_mut();
    v_res_3610_ = lean_grind_cutsat_mk_var(
        v_expr_3598_,
        v_a_3599_,
        v_a_3600_,
        v_a_3601_,
        v_a_3602_,
        v_a_3603_,
        v_a_3604_,
        v_a_3605_,
        v_a_3606_,
        v_a_3607_,
        v_a_3608_,
    );
    return v_res_3610_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(
    mut v_00_u03b2_3611_: *mut LeanObject,
    mut v_x_3612_: *mut LeanObject,
    mut v_x_3613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    v___x_3614_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_3612_, v_x_3613_);
    return v___x_3614_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(
    mut v_00_u03b2_3615_: *mut LeanObject,
    mut v_x_3616_: *mut LeanObject,
    mut v_x_3617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3618_: *mut LeanObject = core::ptr::null_mut();
    v_res_3618_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(
            v_00_u03b2_3615_,
            v_x_3616_,
            v_x_3617_,
        );
    lean_dec_ref(v_x_3617_);
    lean_dec_ref(v_x_3616_);
    return v_res_3618_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(
    mut v_00_u03b2_3619_: *mut LeanObject,
    mut v_x_3620_: *mut LeanObject,
    mut v_x_3621_: *mut LeanObject,
    mut v_x_3622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    v___x_3623_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_3620_, v_x_3621_, v_x_3622_);
    return v___x_3623_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(
    mut v_cls_3624_: *mut LeanObject,
    mut v_msg_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
    mut v___y_3627_: *mut LeanObject,
    mut v___y_3628_: *mut LeanObject,
    mut v___y_3629_: *mut LeanObject,
    mut v___y_3630_: *mut LeanObject,
    mut v___y_3631_: *mut LeanObject,
    mut v___y_3632_: *mut LeanObject,
    mut v___y_3633_: *mut LeanObject,
    mut v___y_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    v___x_3637_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(
        v_cls_3624_,
        v_msg_3625_,
        v___y_3632_,
        v___y_3633_,
        v___y_3634_,
        v___y_3635_,
    );
    return v___x_3637_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(
    mut v_cls_3638_: *mut LeanObject,
    mut v_msg_3639_: *mut LeanObject,
    mut v___y_3640_: *mut LeanObject,
    mut v___y_3641_: *mut LeanObject,
    mut v___y_3642_: *mut LeanObject,
    mut v___y_3643_: *mut LeanObject,
    mut v___y_3644_: *mut LeanObject,
    mut v___y_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
    mut v___y_3648_: *mut LeanObject,
    mut v___y_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3651_: *mut LeanObject = core::ptr::null_mut();
    v_res_3651_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(
        v_cls_3638_,
        v_msg_3639_,
        v___y_3640_,
        v___y_3641_,
        v___y_3642_,
        v___y_3643_,
        v___y_3644_,
        v___y_3645_,
        v___y_3646_,
        v___y_3647_,
        v___y_3648_,
        v___y_3649_,
    );
    lean_dec(v___y_3649_);
    lean_dec_ref(v___y_3648_);
    lean_dec(v___y_3647_);
    lean_dec_ref(v___y_3646_);
    lean_dec(v___y_3645_);
    lean_dec_ref(v___y_3644_);
    lean_dec(v___y_3643_);
    lean_dec_ref(v___y_3642_);
    lean_dec(v___y_3641_);
    lean_dec(v___y_3640_);
    return v_res_3651_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(
    mut v_00_u03b2_3652_: *mut LeanObject,
    mut v_x_3653_: *mut LeanObject,
    mut v_x_3654_: usize,
    mut v_x_3655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    v___x_3656_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_3653_, v_x_3654_, v_x_3655_);
    return v___x_3656_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(
    mut v_00_u03b2_3657_: *mut LeanObject,
    mut v_x_3658_: *mut LeanObject,
    mut v_x_3659_: *mut LeanObject,
    mut v_x_3660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33667__boxed_3661_: usize = 0;
    let mut v_res_3662_: *mut LeanObject = core::ptr::null_mut();
    v_x_33667__boxed_3661_ = lean_unbox_usize(v_x_3659_);
    lean_dec(v_x_3659_);
    v_res_3662_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_3657_, v_x_3658_, v_x_33667__boxed_3661_, v_x_3660_);
    lean_dec_ref(v_x_3660_);
    lean_dec_ref(v_x_3658_);
    return v_res_3662_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(
    mut v_00_u03b2_3663_: *mut LeanObject,
    mut v_x_3664_: *mut LeanObject,
    mut v_x_3665_: usize,
    mut v_x_3666_: usize,
    mut v_x_3667_: *mut LeanObject,
    mut v_x_3668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    v___x_3669_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_3664_, v_x_3665_, v_x_3666_, v_x_3667_, v_x_3668_);
    return v___x_3669_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(
    mut v_00_u03b2_3670_: *mut LeanObject,
    mut v_x_3671_: *mut LeanObject,
    mut v_x_3672_: *mut LeanObject,
    mut v_x_3673_: *mut LeanObject,
    mut v_x_3674_: *mut LeanObject,
    mut v_x_3675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33678__boxed_3676_: usize = 0;
    let mut v_x_33679__boxed_3677_: usize = 0;
    let mut v_res_3678_: *mut LeanObject = core::ptr::null_mut();
    v_x_33678__boxed_3676_ = lean_unbox_usize(v_x_3672_);
    lean_dec(v_x_3672_);
    v_x_33679__boxed_3677_ = lean_unbox_usize(v_x_3673_);
    lean_dec(v_x_3673_);
    v_res_3678_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_3670_, v_x_3671_, v_x_33678__boxed_3676_, v_x_33679__boxed_3677_, v_x_3674_, v_x_3675_);
    return v_res_3678_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3679_: *mut LeanObject,
    mut v_keys_3680_: *mut LeanObject,
    mut v_vals_3681_: *mut LeanObject,
    mut v_heq_3682_: *mut LeanObject,
    mut v_i_3683_: *mut LeanObject,
    mut v_k_3684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    v___x_3685_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_3680_, v_vals_3681_, v_i_3683_, v_k_3684_);
    return v___x_3685_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3686_: *mut LeanObject,
    mut v_keys_3687_: *mut LeanObject,
    mut v_vals_3688_: *mut LeanObject,
    mut v_heq_3689_: *mut LeanObject,
    mut v_i_3690_: *mut LeanObject,
    mut v_k_3691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3692_: *mut LeanObject = core::ptr::null_mut();
    v_res_3692_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_3686_, v_keys_3687_, v_vals_3688_, v_heq_3689_, v_i_3690_, v_k_3691_);
    lean_dec_ref(v_k_3691_);
    lean_dec_ref(v_vals_3688_);
    lean_dec_ref(v_keys_3687_);
    return v_res_3692_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3693_: *mut LeanObject,
    mut v_n_3694_: *mut LeanObject,
    mut v_k_3695_: *mut LeanObject,
    mut v_v_3696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_3694_, v_k_3695_, v_v_3696_);
    return v___x_3697_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(
    mut v_00_u03b2_3698_: *mut LeanObject,
    mut v_depth_3699_: usize,
    mut v_keys_3700_: *mut LeanObject,
    mut v_vals_3701_: *mut LeanObject,
    mut v_heq_3702_: *mut LeanObject,
    mut v_i_3703_: *mut LeanObject,
    mut v_entries_3704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    v___x_3705_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_3699_, v_keys_3700_, v_vals_3701_, v_i_3703_, v_entries_3704_);
    return v___x_3705_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_3706_: *mut LeanObject,
    mut v_depth_3707_: *mut LeanObject,
    mut v_keys_3708_: *mut LeanObject,
    mut v_vals_3709_: *mut LeanObject,
    mut v_heq_3710_: *mut LeanObject,
    mut v_i_3711_: *mut LeanObject,
    mut v_entries_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3713_: usize = 0;
    let mut v_res_3714_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3713_ = lean_unbox_usize(v_depth_3707_);
    lean_dec(v_depth_3707_);
    v_res_3714_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_3706_, v_depth_boxed_3713_, v_keys_3708_, v_vals_3709_, v_heq_3710_, v_i_3711_, v_entries_3712_);
    lean_dec_ref(v_vals_3709_);
    lean_dec_ref(v_keys_3708_);
    return v_res_3714_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(
    mut v_00_u03b2_3715_: *mut LeanObject,
    mut v_x_3716_: *mut LeanObject,
    mut v_x_3717_: *mut LeanObject,
    mut v_x_3718_: *mut LeanObject,
    mut v_x_3719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    v___x_3720_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_3716_, v_x_3717_, v_x_3718_, v_x_3719_);
    return v___x_3720_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    v___x_3724_ = lean_box(0);
    v___x_3725_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1;
    v___x_3726_ = l_Lean_mkConst(v___x_3725_, v___x_3724_);
    return v___x_3726_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(
    mut v_e_3727_: *mut LeanObject,
    mut v_a_3728_: *mut LeanObject,
    mut v_a_3729_: *mut LeanObject,
    mut v_a_3730_: *mut LeanObject,
    mut v_a_3731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3740_: u8 = 0;
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3731_);
                lean_inc_ref(v_a_3730_);
                lean_inc(v_a_3729_);
                lean_inc_ref(v_a_3728_);
                v___x_3733_ =
                    lean_infer_type(v_e_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
                if lean_obj_tag(v___x_3733_) == 0 {
                    v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
                    lean_inc(v_a_3734_);
                    lean_dec_ref_known(v___x_3733_, 1);
                    v___x_3735_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2,
                    );
                    v___x_3736_ = l_Lean_Meta_isExprDefEq(
                        v_a_3734_,
                        v___x_3735_,
                        v_a_3728_,
                        v_a_3729_,
                        v_a_3730_,
                        v_a_3731_,
                    );
                    return v___x_3736_;
                } else {
                    v_a_3737_ = lean_ctor_get(v___x_3733_, 0);
                    v_isSharedCheck_3744_ = (!lean_is_exclusive(v___x_3733_)) as u8;
                    if v_isSharedCheck_3744_ == 0 {
                        v___x_3739_ = v___x_3733_;
                        v_isShared_3740_ = v_isSharedCheck_3744_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3737_);
                        lean_dec(v___x_3733_);
                        v___x_3739_ = lean_box(0);
                        v_isShared_3740_ = v_isSharedCheck_3744_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3740_ == 0 {
                    v___x_3742_ = v___x_3739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
                    v___x_3742_ = v_reuseFailAlloc_3743_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3742_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(
    mut v_e_3745_: *mut LeanObject,
    mut v_a_3746_: *mut LeanObject,
    mut v_a_3747_: *mut LeanObject,
    mut v_a_3748_: *mut LeanObject,
    mut v_a_3749_: *mut LeanObject,
    mut v_a_3750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3751_: *mut LeanObject = core::ptr::null_mut();
    v_res_3751_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(
        v_e_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_,
    );
    lean_dec(v_a_3749_);
    lean_dec_ref(v_a_3748_);
    lean_dec(v_a_3747_);
    lean_dec_ref(v_a_3746_);
    return v_res_3751_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isInt(
    mut v_e_3752_: *mut LeanObject,
    mut v_a_3753_: *mut LeanObject,
    mut v_a_3754_: *mut LeanObject,
    mut v_a_3755_: *mut LeanObject,
    mut v_a_3756_: *mut LeanObject,
    mut v_a_3757_: *mut LeanObject,
    mut v_a_3758_: *mut LeanObject,
    mut v_a_3759_: *mut LeanObject,
    mut v_a_3760_: *mut LeanObject,
    mut v_a_3761_: *mut LeanObject,
    mut v_a_3762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    v___x_3764_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(
        v_e_3752_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_,
    );
    return v___x_3764_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(
    mut v_e_3765_: *mut LeanObject,
    mut v_a_3766_: *mut LeanObject,
    mut v_a_3767_: *mut LeanObject,
    mut v_a_3768_: *mut LeanObject,
    mut v_a_3769_: *mut LeanObject,
    mut v_a_3770_: *mut LeanObject,
    mut v_a_3771_: *mut LeanObject,
    mut v_a_3772_: *mut LeanObject,
    mut v_a_3773_: *mut LeanObject,
    mut v_a_3774_: *mut LeanObject,
    mut v_a_3775_: *mut LeanObject,
    mut v_a_3776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3777_: *mut LeanObject = core::ptr::null_mut();
    v_res_3777_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(
        v_e_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_,
        v_a_3773_, v_a_3774_, v_a_3775_,
    );
    lean_dec(v_a_3775_);
    lean_dec_ref(v_a_3774_);
    lean_dec(v_a_3773_);
    lean_dec_ref(v_a_3772_);
    lean_dec(v_a_3771_);
    lean_dec_ref(v_a_3770_);
    lean_dec(v_a_3769_);
    lean_dec_ref(v_a_3768_);
    lean_dec(v_a_3767_);
    lean_dec(v_a_3766_);
    return v_res_3777_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    v___x_3784_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3;
    v___x_3785_ = l_Lean_stringToMessageData(v___x_3784_);
    return v___x_3785_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(
    mut v_e_3786_: *mut LeanObject,
    mut v_report_3787_: u8,
    mut v_a_3788_: *mut LeanObject,
    mut v_a_3789_: *mut LeanObject,
    mut v_a_3790_: *mut LeanObject,
    mut v_a_3791_: *mut LeanObject,
    mut v_a_3792_: *mut LeanObject,
    mut v_a_3793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3802_: u8 = 0;
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: u8 = 0;
    let mut v_arg_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: u8 = 0;
    let mut v_arg_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: u8 = 0;
    let mut v_arg_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: u8 = 0;
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: u8 = 0;
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: u8 = 0;
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v___x_3831_: u8 = 0;
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: u8 = 0;
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3842_: u8 = 0;
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3846_: u8 = 0;
    let mut v_a_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3854_: u8 = 0;
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3860_: u8 = 0;
    let mut v_a_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3864_: u8 = 0;
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3868_: u8 = 0;
    let mut v_isSharedCheck_3869_: u8 = 0;
    let mut v_a_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3873_: u8 = 0;
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_3786_);
                v___x_3798_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3786_, v_a_3791_);
                if lean_obj_tag(v___x_3798_) == 0 {
                    v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
                    v_isSharedCheck_3869_ = (!lean_is_exclusive(v___x_3798_)) as u8;
                    if v_isSharedCheck_3869_ == 0 {
                        v___x_3801_ = v___x_3798_;
                        v_isShared_3802_ = v_isSharedCheck_3869_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3799_);
                        lean_dec(v___x_3798_);
                        v___x_3801_ = lean_box(0);
                        v_isShared_3802_ = v_isSharedCheck_3869_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3786_);
                    v_a_3870_ = lean_ctor_get(v___x_3798_, 0);
                    v_isSharedCheck_3877_ = (!lean_is_exclusive(v___x_3798_)) as u8;
                    if v_isSharedCheck_3877_ == 0 {
                        v___x_3872_ = v___x_3798_;
                        v_isShared_3873_ = v_isSharedCheck_3877_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3870_);
                        lean_dec(v___x_3798_);
                        v___x_3872_ = lean_box(0);
                        v_isShared_3873_ = v_isSharedCheck_3877_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3796_ = lean_box(0);
                v___x_3797_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3797_, 0, v___x_3796_);
                return v___x_3797_;
            }
            2 => {
                v___x_3808_ = l_Lean_Expr_cleanupAnnotations(v_a_3799_);
                v___x_3809_ = l_Lean_Expr_isApp(v___x_3808_);
                if v___x_3809_ == 0 {
                    lean_dec_ref(v___x_3808_);
                    lean_dec_ref(v_e_3786_);
                    state = 3;
                    continue;
                } else {
                    v_arg_3810_ = lean_ctor_get(v___x_3808_, 1);
                    lean_inc_ref(v_arg_3810_);
                    v___x_3811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3808_);
                    v___x_3812_ = l_Lean_Expr_isApp(v___x_3811_);
                    if v___x_3812_ == 0 {
                        lean_dec_ref(v___x_3811_);
                        lean_dec_ref(v_arg_3810_);
                        lean_dec_ref(v_e_3786_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_3813_ = lean_ctor_get(v___x_3811_, 1);
                        lean_inc_ref(v_arg_3813_);
                        v___x_3814_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3811_);
                        v___x_3815_ = l_Lean_Expr_isApp(v___x_3814_);
                        if v___x_3815_ == 0 {
                            lean_dec_ref(v___x_3814_);
                            lean_dec_ref(v_arg_3813_);
                            lean_dec_ref(v_arg_3810_);
                            lean_dec_ref(v_e_3786_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_3816_ = lean_ctor_get(v___x_3814_, 1);
                            lean_inc_ref(v_arg_3816_);
                            v___x_3817_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3814_);
                            v___x_3818_ = l_Lean_Expr_isApp(v___x_3817_);
                            if v___x_3818_ == 0 {
                                lean_dec_ref(v___x_3817_);
                                lean_dec_ref(v_arg_3816_);
                                lean_dec_ref(v_arg_3813_);
                                lean_dec_ref(v_arg_3810_);
                                lean_dec_ref(v_e_3786_);
                                state = 3;
                                continue;
                            } else {
                                v___x_3819_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3817_);
                                v___x_3820_ = l_Lean_Expr_isApp(v___x_3819_);
                                if v___x_3820_ == 0 {
                                    lean_dec_ref(v___x_3819_);
                                    lean_dec_ref(v_arg_3816_);
                                    lean_dec_ref(v_arg_3813_);
                                    lean_dec_ref(v_arg_3810_);
                                    lean_dec_ref(v_e_3786_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3821_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3819_);
                                    v___x_3822_ = l_Lean_Expr_isApp(v___x_3821_);
                                    if v___x_3822_ == 0 {
                                        lean_dec_ref(v___x_3821_);
                                        lean_dec_ref(v_arg_3816_);
                                        lean_dec_ref(v_arg_3813_);
                                        lean_dec_ref(v_arg_3810_);
                                        lean_dec_ref(v_e_3786_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_3823_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3821_);
                                        v___x_3824_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2;
                                        v___x_3825_ =
                                            l_Lean_Expr_isConstOf(v___x_3823_, v___x_3824_);
                                        lean_dec_ref(v___x_3823_);
                                        if v___x_3825_ == 0 {
                                            lean_dec_ref(v_arg_3816_);
                                            lean_dec_ref(v_arg_3813_);
                                            lean_dec_ref(v_arg_3810_);
                                            lean_dec_ref(v_e_3786_);
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_del_object(v___x_3801_);
                                            v___x_3826_ =
                                                l_Lean_Meta_Structural_isInstHAddInt___redArg(
                                                    v_arg_3816_,
                                                    v_a_3791_,
                                                );
                                            if lean_obj_tag(v___x_3826_) == 0 {
                                                v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
                                                v_isSharedCheck_3860_ =
                                                    (!lean_is_exclusive(v___x_3826_)) as u8;
                                                if v_isSharedCheck_3860_ == 0 {
                                                    v___x_3829_ = v___x_3826_;
                                                    v_isShared_3830_ = v_isSharedCheck_3860_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3827_);
                                                    lean_dec(v___x_3826_);
                                                    v___x_3829_ = lean_box(0);
                                                    v_isShared_3830_ = v_isSharedCheck_3860_;
                                                    state = 5;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_3813_);
                                                lean_dec_ref(v_arg_3810_);
                                                lean_dec_ref(v_e_3786_);
                                                v_a_3861_ = lean_ctor_get(v___x_3826_, 0);
                                                v_isSharedCheck_3868_ =
                                                    (!lean_is_exclusive(v___x_3826_)) as u8;
                                                if v_isSharedCheck_3868_ == 0 {
                                                    v___x_3863_ = v___x_3826_;
                                                    v_isShared_3864_ = v_isSharedCheck_3868_;
                                                    state = 11;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3861_);
                                                    lean_dec(v___x_3826_);
                                                    v___x_3863_ = lean_box(0);
                                                    v_isShared_3864_ = v_isSharedCheck_3868_;
                                                    state = 11;
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
            3 => {
                v___x_3804_ = lean_box(0);
                if v_isShared_3802_ == 0 {
                    lean_ctor_set(v___x_3801_, 0, v___x_3804_);
                    v___x_3806_ = v___x_3801_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
                    v___x_3806_ = v_reuseFailAlloc_3807_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3806_;
            }
            5 => {
                v___x_3831_ = (lean_unbox(v_a_3827_) as u8);
                lean_dec(v_a_3827_);
                if v___x_3831_ == 0 {
                    lean_del_object(v___x_3829_);
                    lean_dec_ref(v_arg_3813_);
                    lean_dec_ref(v_arg_3810_);
                    if v_report_3787_ == 0 {
                        lean_dec_ref(v_e_3786_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3832_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3788_);
                        if lean_obj_tag(v___x_3832_) == 0 {
                            v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
                            lean_inc(v_a_3833_);
                            lean_dec_ref_known(v___x_3832_, 1);
                            v___x_3834_ = (lean_unbox(v_a_3833_) as u8);
                            lean_dec(v_a_3833_);
                            if v___x_3834_ == 0 {
                                lean_dec_ref(v_e_3786_);
                                state = 1;
                                continue;
                            } else {
                                v___x_3835_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
                                v___x_3836_ = l_Lean_indentExpr(v_e_3786_);
                                v___x_3837_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3837_, 0, v___x_3835_);
                                lean_ctor_set(v___x_3837_, 1, v___x_3836_);
                                v___x_3838_ = l_Lean_Meta_Sym_reportIssue(
                                    v___x_3837_,
                                    v_a_3788_,
                                    v_a_3789_,
                                    v_a_3790_,
                                    v_a_3791_,
                                    v_a_3792_,
                                    v_a_3793_,
                                );
                                if lean_obj_tag(v___x_3838_) == 0 {
                                    lean_dec_ref_known(v___x_3838_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
                                    v_isSharedCheck_3846_ = (!lean_is_exclusive(v___x_3838_)) as u8;
                                    if v_isSharedCheck_3846_ == 0 {
                                        v___x_3841_ = v___x_3838_;
                                        v_isShared_3842_ = v_isSharedCheck_3846_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3839_);
                                        lean_dec(v___x_3838_);
                                        v___x_3841_ = lean_box(0);
                                        v_isShared_3842_ = v_isSharedCheck_3846_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v_e_3786_);
                            v_a_3847_ = lean_ctor_get(v___x_3832_, 0);
                            v_isSharedCheck_3854_ = (!lean_is_exclusive(v___x_3832_)) as u8;
                            if v_isSharedCheck_3854_ == 0 {
                                v___x_3849_ = v___x_3832_;
                                v_isShared_3850_ = v_isSharedCheck_3854_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_3847_);
                                lean_dec(v___x_3832_);
                                v___x_3849_ = lean_box(0);
                                v_isShared_3850_ = v_isSharedCheck_3854_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_3786_);
                    v___x_3855_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3855_, 0, v_arg_3813_);
                    lean_ctor_set(v___x_3855_, 1, v_arg_3810_);
                    v___x_3856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3856_, 0, v___x_3855_);
                    if v_isShared_3830_ == 0 {
                        lean_ctor_set(v___x_3829_, 0, v___x_3856_);
                        v___x_3858_ = v___x_3829_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
                        v___x_3858_ = v_reuseFailAlloc_3859_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3842_ == 0 {
                    v___x_3844_ = v___x_3841_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
                    v___x_3844_ = v_reuseFailAlloc_3845_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3844_;
            }
            8 => {
                if v_isShared_3850_ == 0 {
                    v___x_3852_ = v___x_3849_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
                    v___x_3852_ = v_reuseFailAlloc_3853_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3852_;
            }
            10 => {
                return v___x_3858_;
            }
            11 => {
                if v_isShared_3864_ == 0 {
                    v___x_3866_ = v___x_3863_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
                    v___x_3866_ = v_reuseFailAlloc_3867_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3866_;
            }
            13 => {
                if v_isShared_3873_ == 0 {
                    v___x_3875_ = v___x_3872_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
                    v___x_3875_ = v_reuseFailAlloc_3876_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(
    mut v_e_3878_: *mut LeanObject,
    mut v_report_3879_: *mut LeanObject,
    mut v_a_3880_: *mut LeanObject,
    mut v_a_3881_: *mut LeanObject,
    mut v_a_3882_: *mut LeanObject,
    mut v_a_3883_: *mut LeanObject,
    mut v_a_3884_: *mut LeanObject,
    mut v_a_3885_: *mut LeanObject,
    mut v_a_3886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_report_boxed_3887_: u8 = 0;
    let mut v_res_3888_: *mut LeanObject = core::ptr::null_mut();
    v_report_boxed_3887_ = (lean_unbox(v_report_3879_) as u8);
    v_res_3888_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(
        v_e_3878_,
        v_report_boxed_3887_,
        v_a_3880_,
        v_a_3881_,
        v_a_3882_,
        v_a_3883_,
        v_a_3884_,
        v_a_3885_,
    );
    lean_dec(v_a_3885_);
    lean_dec_ref(v_a_3884_);
    lean_dec(v_a_3883_);
    lean_dec_ref(v_a_3882_);
    lean_dec(v_a_3881_);
    lean_dec_ref(v_a_3880_);
    return v_res_3888_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(
    mut v_e_3889_: *mut LeanObject,
    mut v_report_3890_: u8,
    mut v_a_3891_: *mut LeanObject,
    mut v_a_3892_: *mut LeanObject,
    mut v_a_3893_: *mut LeanObject,
    mut v_a_3894_: *mut LeanObject,
    mut v_a_3895_: *mut LeanObject,
    mut v_a_3896_: *mut LeanObject,
    mut v_a_3897_: *mut LeanObject,
    mut v_a_3898_: *mut LeanObject,
    mut v_a_3899_: *mut LeanObject,
    mut v_a_3900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    v___x_3902_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(
        v_e_3889_,
        v_report_3890_,
        v_a_3895_,
        v_a_3896_,
        v_a_3897_,
        v_a_3898_,
        v_a_3899_,
        v_a_3900_,
    );
    return v___x_3902_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(
    mut v_e_3903_: *mut LeanObject,
    mut v_report_3904_: *mut LeanObject,
    mut v_a_3905_: *mut LeanObject,
    mut v_a_3906_: *mut LeanObject,
    mut v_a_3907_: *mut LeanObject,
    mut v_a_3908_: *mut LeanObject,
    mut v_a_3909_: *mut LeanObject,
    mut v_a_3910_: *mut LeanObject,
    mut v_a_3911_: *mut LeanObject,
    mut v_a_3912_: *mut LeanObject,
    mut v_a_3913_: *mut LeanObject,
    mut v_a_3914_: *mut LeanObject,
    mut v_a_3915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_report_boxed_3916_: u8 = 0;
    let mut v_res_3917_: *mut LeanObject = core::ptr::null_mut();
    v_report_boxed_3916_ = (lean_unbox(v_report_3904_) as u8);
    v_res_3917_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(
        v_e_3903_,
        v_report_boxed_3916_,
        v_a_3905_,
        v_a_3906_,
        v_a_3907_,
        v_a_3908_,
        v_a_3909_,
        v_a_3910_,
        v_a_3911_,
        v_a_3912_,
        v_a_3913_,
        v_a_3914_,
    );
    lean_dec(v_a_3914_);
    lean_dec_ref(v_a_3913_);
    lean_dec(v_a_3912_);
    lean_dec_ref(v_a_3911_);
    lean_dec(v_a_3910_);
    lean_dec_ref(v_a_3909_);
    lean_dec(v_a_3908_);
    lean_dec_ref(v_a_3907_);
    lean_dec(v_a_3906_);
    lean_dec(v_a_3905_);
    return v_res_3917_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(
    mut v_e_3918_: *mut LeanObject,
    mut v_a_3919_: *mut LeanObject,
    mut v_a_3920_: *mut LeanObject,
    mut v_a_3921_: *mut LeanObject,
    mut v_a_3922_: *mut LeanObject,
    mut v_a_3923_: *mut LeanObject,
    mut v_a_3924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: u8 = 0;
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3941_: u8 = 0;
    let mut v_a_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3926_ = 0;
                v___x_3927_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(
                    v_e_3918_,
                    v___x_3926_,
                    v_a_3919_,
                    v_a_3920_,
                    v_a_3921_,
                    v_a_3922_,
                    v_a_3923_,
                    v_a_3924_,
                );
                if lean_obj_tag(v___x_3927_) == 0 {
                    v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
                    v_isSharedCheck_3941_ = (!lean_is_exclusive(v___x_3927_)) as u8;
                    if v_isSharedCheck_3941_ == 0 {
                        v___x_3930_ = v___x_3927_;
                        v_isShared_3931_ = v_isSharedCheck_3941_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3928_);
                        lean_dec(v___x_3927_);
                        v___x_3930_ = lean_box(0);
                        v_isShared_3931_ = v_isSharedCheck_3941_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3942_ = lean_ctor_get(v___x_3927_, 0);
                    v_isSharedCheck_3949_ = (!lean_is_exclusive(v___x_3927_)) as u8;
                    if v_isSharedCheck_3949_ == 0 {
                        v___x_3944_ = v___x_3927_;
                        v_isShared_3945_ = v_isSharedCheck_3949_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3942_);
                        lean_dec(v___x_3927_);
                        v___x_3944_ = lean_box(0);
                        v_isShared_3945_ = v_isSharedCheck_3949_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3928_) == 0 {
                    v___x_3932_ = lean_box((v___x_3926_) as usize);
                    if v_isShared_3931_ == 0 {
                        lean_ctor_set(v___x_3930_, 0, v___x_3932_);
                        v___x_3934_ = v___x_3930_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
                        v___x_3934_ = v_reuseFailAlloc_3935_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_3928_, 1);
                    v___x_3936_ = 1;
                    v___x_3937_ = lean_box((v___x_3936_) as usize);
                    if v_isShared_3931_ == 0 {
                        lean_ctor_set(v___x_3930_, 0, v___x_3937_);
                        v___x_3939_ = v___x_3930_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
                        v___x_3939_ = v_reuseFailAlloc_3940_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3934_;
            }
            3 => {
                return v___x_3939_;
            }
            4 => {
                if v_isShared_3945_ == 0 {
                    v___x_3947_ = v___x_3944_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
                    v___x_3947_ = v_reuseFailAlloc_3948_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(
    mut v_e_3950_: *mut LeanObject,
    mut v_a_3951_: *mut LeanObject,
    mut v_a_3952_: *mut LeanObject,
    mut v_a_3953_: *mut LeanObject,
    mut v_a_3954_: *mut LeanObject,
    mut v_a_3955_: *mut LeanObject,
    mut v_a_3956_: *mut LeanObject,
    mut v_a_3957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3958_: *mut LeanObject = core::ptr::null_mut();
    v_res_3958_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(
        v_e_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_,
    );
    lean_dec(v_a_3956_);
    lean_dec_ref(v_a_3955_);
    lean_dec(v_a_3954_);
    lean_dec_ref(v_a_3953_);
    lean_dec(v_a_3952_);
    lean_dec_ref(v_a_3951_);
    return v_res_3958_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isAdd(
    mut v_e_3959_: *mut LeanObject,
    mut v_a_3960_: *mut LeanObject,
    mut v_a_3961_: *mut LeanObject,
    mut v_a_3962_: *mut LeanObject,
    mut v_a_3963_: *mut LeanObject,
    mut v_a_3964_: *mut LeanObject,
    mut v_a_3965_: *mut LeanObject,
    mut v_a_3966_: *mut LeanObject,
    mut v_a_3967_: *mut LeanObject,
    mut v_a_3968_: *mut LeanObject,
    mut v_a_3969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    v___x_3971_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(
        v_e_3959_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_,
    );
    return v___x_3971_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(
    mut v_e_3972_: *mut LeanObject,
    mut v_a_3973_: *mut LeanObject,
    mut v_a_3974_: *mut LeanObject,
    mut v_a_3975_: *mut LeanObject,
    mut v_a_3976_: *mut LeanObject,
    mut v_a_3977_: *mut LeanObject,
    mut v_a_3978_: *mut LeanObject,
    mut v_a_3979_: *mut LeanObject,
    mut v_a_3980_: *mut LeanObject,
    mut v_a_3981_: *mut LeanObject,
    mut v_a_3982_: *mut LeanObject,
    mut v_a_3983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3984_: *mut LeanObject = core::ptr::null_mut();
    v_res_3984_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(
        v_e_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_,
        v_a_3980_, v_a_3981_, v_a_3982_,
    );
    lean_dec(v_a_3982_);
    lean_dec_ref(v_a_3981_);
    lean_dec(v_a_3980_);
    lean_dec_ref(v_a_3979_);
    lean_dec(v_a_3978_);
    lean_dec_ref(v_a_3977_);
    lean_dec(v_a_3976_);
    lean_dec_ref(v_a_3975_);
    lean_dec(v_a_3974_);
    lean_dec(v_a_3973_);
    return v_res_3984_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(
    mut v_e_3985_: *mut LeanObject,
    mut v_report_3986_: u8,
    mut v_a_3987_: *mut LeanObject,
    mut v_a_3988_: *mut LeanObject,
    mut v_a_3989_: *mut LeanObject,
    mut v_a_3990_: *mut LeanObject,
    mut v_a_3991_: *mut LeanObject,
    mut v_a_3992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4001_: u8 = 0;
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: u8 = 0;
    let mut v_arg_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: u8 = 0;
    let mut v_arg_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: u8 = 0;
    let mut v_arg_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: u8 = 0;
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: u8 = 0;
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: u8 = 0;
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4038_: u8 = 0;
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4042_: u8 = 0;
    let mut v_a_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4050_: u8 = 0;
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v_val_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v_a_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4076_: u8 = 0;
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4080_: u8 = 0;
    let mut v_a_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4084_: u8 = 0;
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4088_: u8 = 0;
    let mut v_isSharedCheck_4089_: u8 = 0;
    let mut v_a_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4093_: u8 = 0;
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_3985_);
                v___x_3997_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3985_, v_a_3990_);
                if lean_obj_tag(v___x_3997_) == 0 {
                    v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
                    v_isSharedCheck_4089_ = (!lean_is_exclusive(v___x_3997_)) as u8;
                    if v_isSharedCheck_4089_ == 0 {
                        v___x_4000_ = v___x_3997_;
                        v_isShared_4001_ = v_isSharedCheck_4089_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3998_);
                        lean_dec(v___x_3997_);
                        v___x_4000_ = lean_box(0);
                        v_isShared_4001_ = v_isSharedCheck_4089_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3985_);
                    v_a_4090_ = lean_ctor_get(v___x_3997_, 0);
                    v_isSharedCheck_4097_ = (!lean_is_exclusive(v___x_3997_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v___x_4092_ = v___x_3997_;
                        v_isShared_4093_ = v_isSharedCheck_4097_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_4090_);
                        lean_dec(v___x_3997_);
                        v___x_4092_ = lean_box(0);
                        v_isShared_4093_ = v_isSharedCheck_4097_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3995_ = lean_box(0);
                v___x_3996_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3996_, 0, v___x_3995_);
                return v___x_3996_;
            }
            2 => {
                v___x_4007_ = l_Lean_Expr_cleanupAnnotations(v_a_3998_);
                v___x_4008_ = l_Lean_Expr_isApp(v___x_4007_);
                if v___x_4008_ == 0 {
                    lean_dec_ref(v___x_4007_);
                    lean_dec_ref(v_e_3985_);
                    state = 3;
                    continue;
                } else {
                    v_arg_4009_ = lean_ctor_get(v___x_4007_, 1);
                    lean_inc_ref(v_arg_4009_);
                    v___x_4010_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4007_);
                    v___x_4011_ = l_Lean_Expr_isApp(v___x_4010_);
                    if v___x_4011_ == 0 {
                        lean_dec_ref(v___x_4010_);
                        lean_dec_ref(v_arg_4009_);
                        lean_dec_ref(v_e_3985_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_4012_ = lean_ctor_get(v___x_4010_, 1);
                        lean_inc_ref(v_arg_4012_);
                        v___x_4013_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4010_);
                        v___x_4014_ = l_Lean_Expr_isApp(v___x_4013_);
                        if v___x_4014_ == 0 {
                            lean_dec_ref(v___x_4013_);
                            lean_dec_ref(v_arg_4012_);
                            lean_dec_ref(v_arg_4009_);
                            lean_dec_ref(v_e_3985_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_4015_ = lean_ctor_get(v___x_4013_, 1);
                            lean_inc_ref(v_arg_4015_);
                            v___x_4016_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4013_);
                            v___x_4017_ = l_Lean_Expr_isApp(v___x_4016_);
                            if v___x_4017_ == 0 {
                                lean_dec_ref(v___x_4016_);
                                lean_dec_ref(v_arg_4015_);
                                lean_dec_ref(v_arg_4012_);
                                lean_dec_ref(v_arg_4009_);
                                lean_dec_ref(v_e_3985_);
                                state = 3;
                                continue;
                            } else {
                                v___x_4018_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4016_);
                                v___x_4019_ = l_Lean_Expr_isApp(v___x_4018_);
                                if v___x_4019_ == 0 {
                                    lean_dec_ref(v___x_4018_);
                                    lean_dec_ref(v_arg_4015_);
                                    lean_dec_ref(v_arg_4012_);
                                    lean_dec_ref(v_arg_4009_);
                                    lean_dec_ref(v_e_3985_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_4020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4018_);
                                    v___x_4021_ = l_Lean_Expr_isApp(v___x_4020_);
                                    if v___x_4021_ == 0 {
                                        lean_dec_ref(v___x_4020_);
                                        lean_dec_ref(v_arg_4015_);
                                        lean_dec_ref(v_arg_4012_);
                                        lean_dec_ref(v_arg_4009_);
                                        lean_dec_ref(v_e_3985_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_4022_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_4020_);
                                        v___x_4023_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11;
                                        v___x_4024_ =
                                            l_Lean_Expr_isConstOf(v___x_4022_, v___x_4023_);
                                        lean_dec_ref(v___x_4022_);
                                        if v___x_4024_ == 0 {
                                            lean_dec_ref(v_arg_4015_);
                                            lean_dec_ref(v_arg_4012_);
                                            lean_dec_ref(v_arg_4009_);
                                            lean_dec_ref(v_e_3985_);
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_del_object(v___x_4000_);
                                            v___x_4025_ =
                                                l_Lean_Meta_Structural_isInstHMulInt___redArg(
                                                    v_arg_4015_,
                                                    v_a_3990_,
                                                );
                                            if lean_obj_tag(v___x_4025_) == 0 {
                                                v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
                                                lean_inc(v_a_4026_);
                                                lean_dec_ref_known(v___x_4025_, 1);
                                                v___x_4027_ = (lean_unbox(v_a_4026_) as u8);
                                                lean_dec(v_a_4026_);
                                                if v___x_4027_ == 0 {
                                                    lean_dec_ref(v_arg_4012_);
                                                    lean_dec_ref(v_arg_4009_);
                                                    if v_report_3986_ == 0 {
                                                        lean_dec_ref(v_e_3985_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_4028_ =
                                                            l_Lean_Meta_Sym_getConfig___redArg(
                                                                v_a_3987_,
                                                            );
                                                        if lean_obj_tag(v___x_4028_) == 0 {
                                                            v_a_4029_ =
                                                                lean_ctor_get(v___x_4028_, 0);
                                                            lean_inc(v_a_4029_);
                                                            lean_dec_ref_known(v___x_4028_, 1);
                                                            v___x_4030_ =
                                                                (lean_unbox(v_a_4029_) as u8);
                                                            lean_dec(v_a_4029_);
                                                            if v___x_4030_ == 0 {
                                                                lean_dec_ref(v_e_3985_);
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_4031_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
                                                                v___x_4032_ =
                                                                    l_Lean_indentExpr(v_e_3985_);
                                                                v___x_4033_ = lean_alloc_ctor(
                                                                    7,
                                                                    2,
                                                                    (0) as u32,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_4033_,
                                                                    0,
                                                                    v___x_4031_,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_4033_,
                                                                    1,
                                                                    v___x_4032_,
                                                                );
                                                                v___x_4034_ =
                                                                    l_Lean_Meta_Sym_reportIssue(
                                                                        v___x_4033_,
                                                                        v_a_3987_,
                                                                        v_a_3988_,
                                                                        v_a_3989_,
                                                                        v_a_3990_,
                                                                        v_a_3991_,
                                                                        v_a_3992_,
                                                                    );
                                                                if lean_obj_tag(v___x_4034_) == 0 {
                                                                    lean_dec_ref_known(
                                                                        v___x_4034_,
                                                                        1,
                                                                    );
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    v_a_4035_ = lean_ctor_get(
                                                                        v___x_4034_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_4042_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_4034_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_4042_ == 0 {
                                                                        v___x_4037_ = v___x_4034_;
                                                                        v_isShared_4038_ =
                                                                            v_isSharedCheck_4042_;
                                                                        state = 5;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_4035_);
                                                                        lean_dec(v___x_4034_);
                                                                        v___x_4037_ = lean_box(0);
                                                                        v_isShared_4038_ =
                                                                            v_isSharedCheck_4042_;
                                                                        state = 5;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_e_3985_);
                                                            v_a_4043_ =
                                                                lean_ctor_get(v___x_4028_, 0);
                                                            v_isSharedCheck_4050_ =
                                                                (!lean_is_exclusive(v___x_4028_))
                                                                    as u8;
                                                            if v_isSharedCheck_4050_ == 0 {
                                                                v___x_4045_ = v___x_4028_;
                                                                v_isShared_4046_ =
                                                                    v_isSharedCheck_4050_;
                                                                state = 7;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_4043_);
                                                                lean_dec(v___x_4028_);
                                                                v___x_4045_ = lean_box(0);
                                                                v_isShared_4046_ =
                                                                    v_isSharedCheck_4050_;
                                                                state = 7;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v_e_3985_);
                                                    v___x_4051_ = l_Lean_Meta_getIntValue_x3f(
                                                        v_arg_4012_,
                                                        v_a_3989_,
                                                        v_a_3990_,
                                                        v_a_3991_,
                                                        v_a_3992_,
                                                    );
                                                    if lean_obj_tag(v___x_4051_) == 0 {
                                                        v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
                                                        v_isSharedCheck_4072_ =
                                                            (!lean_is_exclusive(v___x_4051_)) as u8;
                                                        if v_isSharedCheck_4072_ == 0 {
                                                            v___x_4054_ = v___x_4051_;
                                                            v_isShared_4055_ =
                                                                v_isSharedCheck_4072_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4052_);
                                                            lean_dec(v___x_4051_);
                                                            v___x_4054_ = lean_box(0);
                                                            v_isShared_4055_ =
                                                                v_isSharedCheck_4072_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_4009_);
                                                        v_a_4073_ = lean_ctor_get(v___x_4051_, 0);
                                                        v_isSharedCheck_4080_ =
                                                            (!lean_is_exclusive(v___x_4051_)) as u8;
                                                        if v_isSharedCheck_4080_ == 0 {
                                                            v___x_4075_ = v___x_4051_;
                                                            v_isShared_4076_ =
                                                                v_isSharedCheck_4080_;
                                                            state = 14;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4073_);
                                                            lean_dec(v___x_4051_);
                                                            v___x_4075_ = lean_box(0);
                                                            v_isShared_4076_ =
                                                                v_isSharedCheck_4080_;
                                                            state = 14;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_4012_);
                                                lean_dec_ref(v_arg_4009_);
                                                lean_dec_ref(v_e_3985_);
                                                v_a_4081_ = lean_ctor_get(v___x_4025_, 0);
                                                v_isSharedCheck_4088_ =
                                                    (!lean_is_exclusive(v___x_4025_)) as u8;
                                                if v_isSharedCheck_4088_ == 0 {
                                                    v___x_4083_ = v___x_4025_;
                                                    v_isShared_4084_ = v_isSharedCheck_4088_;
                                                    state = 16;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4081_);
                                                    lean_dec(v___x_4025_);
                                                    v___x_4083_ = lean_box(0);
                                                    v_isShared_4084_ = v_isSharedCheck_4088_;
                                                    state = 16;
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
            3 => {
                v___x_4003_ = lean_box(0);
                if v_isShared_4001_ == 0 {
                    lean_ctor_set(v___x_4000_, 0, v___x_4003_);
                    v___x_4005_ = v___x_4000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_4003_);
                    v___x_4005_ = v_reuseFailAlloc_4006_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4005_;
            }
            5 => {
                if v_isShared_4038_ == 0 {
                    v___x_4040_ = v___x_4037_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
                    v___x_4040_ = v_reuseFailAlloc_4041_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4040_;
            }
            7 => {
                if v_isShared_4046_ == 0 {
                    v___x_4048_ = v___x_4045_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
                    v___x_4048_ = v_reuseFailAlloc_4049_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4048_;
            }
            9 => {
                if lean_obj_tag(v_a_4052_) == 1 {
                    v_val_4056_ = lean_ctor_get(v_a_4052_, 0);
                    v_isSharedCheck_4067_ = (!lean_is_exclusive(v_a_4052_)) as u8;
                    if v_isSharedCheck_4067_ == 0 {
                        v___x_4058_ = v_a_4052_;
                        v_isShared_4059_ = v_isSharedCheck_4067_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_val_4056_);
                        lean_dec(v_a_4052_);
                        v___x_4058_ = lean_box(0);
                        v_isShared_4059_ = v_isSharedCheck_4067_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4052_);
                    lean_dec_ref(v_arg_4009_);
                    v___x_4068_ = lean_box(0);
                    if v_isShared_4055_ == 0 {
                        lean_ctor_set(v___x_4054_, 0, v___x_4068_);
                        v___x_4070_ = v___x_4054_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
                        v___x_4070_ = v_reuseFailAlloc_4071_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4060_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4060_, 0, v_val_4056_);
                lean_ctor_set(v___x_4060_, 1, v_arg_4009_);
                if v_isShared_4059_ == 0 {
                    lean_ctor_set(v___x_4058_, 0, v___x_4060_);
                    v___x_4062_ = v___x_4058_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4060_);
                    v___x_4062_ = v_reuseFailAlloc_4066_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4055_ == 0 {
                    lean_ctor_set(v___x_4054_, 0, v___x_4062_);
                    v___x_4064_ = v___x_4054_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4062_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4064_;
            }
            13 => {
                return v___x_4070_;
            }
            14 => {
                if v_isShared_4076_ == 0 {
                    v___x_4078_ = v___x_4075_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
                    v___x_4078_ = v_reuseFailAlloc_4079_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4078_;
            }
            16 => {
                if v_isShared_4084_ == 0 {
                    v___x_4086_ = v___x_4083_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
                    v___x_4086_ = v_reuseFailAlloc_4087_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4086_;
            }
            18 => {
                if v_isShared_4093_ == 0 {
                    v___x_4095_ = v___x_4092_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
                    v___x_4095_ = v_reuseFailAlloc_4096_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(
    mut v_e_4098_: *mut LeanObject,
    mut v_report_4099_: *mut LeanObject,
    mut v_a_4100_: *mut LeanObject,
    mut v_a_4101_: *mut LeanObject,
    mut v_a_4102_: *mut LeanObject,
    mut v_a_4103_: *mut LeanObject,
    mut v_a_4104_: *mut LeanObject,
    mut v_a_4105_: *mut LeanObject,
    mut v_a_4106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_report_boxed_4107_: u8 = 0;
    let mut v_res_4108_: *mut LeanObject = core::ptr::null_mut();
    v_report_boxed_4107_ = (lean_unbox(v_report_4099_) as u8);
    v_res_4108_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(
        v_e_4098_,
        v_report_boxed_4107_,
        v_a_4100_,
        v_a_4101_,
        v_a_4102_,
        v_a_4103_,
        v_a_4104_,
        v_a_4105_,
    );
    lean_dec(v_a_4105_);
    lean_dec_ref(v_a_4104_);
    lean_dec(v_a_4103_);
    lean_dec_ref(v_a_4102_);
    lean_dec(v_a_4101_);
    lean_dec_ref(v_a_4100_);
    return v_res_4108_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(
    mut v_e_4109_: *mut LeanObject,
    mut v_report_4110_: u8,
    mut v_a_4111_: *mut LeanObject,
    mut v_a_4112_: *mut LeanObject,
    mut v_a_4113_: *mut LeanObject,
    mut v_a_4114_: *mut LeanObject,
    mut v_a_4115_: *mut LeanObject,
    mut v_a_4116_: *mut LeanObject,
    mut v_a_4117_: *mut LeanObject,
    mut v_a_4118_: *mut LeanObject,
    mut v_a_4119_: *mut LeanObject,
    mut v_a_4120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    v___x_4122_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(
        v_e_4109_,
        v_report_4110_,
        v_a_4115_,
        v_a_4116_,
        v_a_4117_,
        v_a_4118_,
        v_a_4119_,
        v_a_4120_,
    );
    return v___x_4122_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(
    mut v_e_4123_: *mut LeanObject,
    mut v_report_4124_: *mut LeanObject,
    mut v_a_4125_: *mut LeanObject,
    mut v_a_4126_: *mut LeanObject,
    mut v_a_4127_: *mut LeanObject,
    mut v_a_4128_: *mut LeanObject,
    mut v_a_4129_: *mut LeanObject,
    mut v_a_4130_: *mut LeanObject,
    mut v_a_4131_: *mut LeanObject,
    mut v_a_4132_: *mut LeanObject,
    mut v_a_4133_: *mut LeanObject,
    mut v_a_4134_: *mut LeanObject,
    mut v_a_4135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_report_boxed_4136_: u8 = 0;
    let mut v_res_4137_: *mut LeanObject = core::ptr::null_mut();
    v_report_boxed_4136_ = (lean_unbox(v_report_4124_) as u8);
    v_res_4137_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(
        v_e_4123_,
        v_report_boxed_4136_,
        v_a_4125_,
        v_a_4126_,
        v_a_4127_,
        v_a_4128_,
        v_a_4129_,
        v_a_4130_,
        v_a_4131_,
        v_a_4132_,
        v_a_4133_,
        v_a_4134_,
    );
    lean_dec(v_a_4134_);
    lean_dec_ref(v_a_4133_);
    lean_dec(v_a_4132_);
    lean_dec_ref(v_a_4131_);
    lean_dec(v_a_4130_);
    lean_dec_ref(v_a_4129_);
    lean_dec(v_a_4128_);
    lean_dec_ref(v_a_4127_);
    lean_dec(v_a_4126_);
    lean_dec(v_a_4125_);
    return v_res_4137_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(
    mut v_e_4138_: *mut LeanObject,
    mut v_a_4139_: *mut LeanObject,
    mut v_a_4140_: *mut LeanObject,
    mut v_a_4141_: *mut LeanObject,
    mut v_a_4142_: *mut LeanObject,
    mut v_a_4143_: *mut LeanObject,
    mut v_a_4144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4146_: u8 = 0;
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: u8 = 0;
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4161_: u8 = 0;
    let mut v_a_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4165_: u8 = 0;
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4146_ = 0;
                v___x_4147_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(
                    v_e_4138_,
                    v___x_4146_,
                    v_a_4139_,
                    v_a_4140_,
                    v_a_4141_,
                    v_a_4142_,
                    v_a_4143_,
                    v_a_4144_,
                );
                if lean_obj_tag(v___x_4147_) == 0 {
                    v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
                    v_isSharedCheck_4161_ = (!lean_is_exclusive(v___x_4147_)) as u8;
                    if v_isSharedCheck_4161_ == 0 {
                        v___x_4150_ = v___x_4147_;
                        v_isShared_4151_ = v_isSharedCheck_4161_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4148_);
                        lean_dec(v___x_4147_);
                        v___x_4150_ = lean_box(0);
                        v_isShared_4151_ = v_isSharedCheck_4161_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4162_ = lean_ctor_get(v___x_4147_, 0);
                    v_isSharedCheck_4169_ = (!lean_is_exclusive(v___x_4147_)) as u8;
                    if v_isSharedCheck_4169_ == 0 {
                        v___x_4164_ = v___x_4147_;
                        v_isShared_4165_ = v_isSharedCheck_4169_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4162_);
                        lean_dec(v___x_4147_);
                        v___x_4164_ = lean_box(0);
                        v_isShared_4165_ = v_isSharedCheck_4169_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4148_) == 0 {
                    v___x_4152_ = lean_box((v___x_4146_) as usize);
                    if v_isShared_4151_ == 0 {
                        lean_ctor_set(v___x_4150_, 0, v___x_4152_);
                        v___x_4154_ = v___x_4150_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4152_);
                        v___x_4154_ = v_reuseFailAlloc_4155_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_4148_, 1);
                    v___x_4156_ = 1;
                    v___x_4157_ = lean_box((v___x_4156_) as usize);
                    if v_isShared_4151_ == 0 {
                        lean_ctor_set(v___x_4150_, 0, v___x_4157_);
                        v___x_4159_ = v___x_4150_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4157_);
                        v___x_4159_ = v_reuseFailAlloc_4160_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4154_;
            }
            3 => {
                return v___x_4159_;
            }
            4 => {
                if v_isShared_4165_ == 0 {
                    v___x_4167_ = v___x_4164_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
                    v___x_4167_ = v_reuseFailAlloc_4168_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(
    mut v_e_4170_: *mut LeanObject,
    mut v_a_4171_: *mut LeanObject,
    mut v_a_4172_: *mut LeanObject,
    mut v_a_4173_: *mut LeanObject,
    mut v_a_4174_: *mut LeanObject,
    mut v_a_4175_: *mut LeanObject,
    mut v_a_4176_: *mut LeanObject,
    mut v_a_4177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4178_: *mut LeanObject = core::ptr::null_mut();
    v_res_4178_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(
        v_e_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_,
    );
    lean_dec(v_a_4176_);
    lean_dec_ref(v_a_4175_);
    lean_dec(v_a_4174_);
    lean_dec_ref(v_a_4173_);
    lean_dec(v_a_4172_);
    lean_dec_ref(v_a_4171_);
    return v_res_4178_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isMul(
    mut v_e_4179_: *mut LeanObject,
    mut v_a_4180_: *mut LeanObject,
    mut v_a_4181_: *mut LeanObject,
    mut v_a_4182_: *mut LeanObject,
    mut v_a_4183_: *mut LeanObject,
    mut v_a_4184_: *mut LeanObject,
    mut v_a_4185_: *mut LeanObject,
    mut v_a_4186_: *mut LeanObject,
    mut v_a_4187_: *mut LeanObject,
    mut v_a_4188_: *mut LeanObject,
    mut v_a_4189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    v___x_4191_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(
        v_e_4179_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_,
    );
    return v___x_4191_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(
    mut v_e_4192_: *mut LeanObject,
    mut v_a_4193_: *mut LeanObject,
    mut v_a_4194_: *mut LeanObject,
    mut v_a_4195_: *mut LeanObject,
    mut v_a_4196_: *mut LeanObject,
    mut v_a_4197_: *mut LeanObject,
    mut v_a_4198_: *mut LeanObject,
    mut v_a_4199_: *mut LeanObject,
    mut v_a_4200_: *mut LeanObject,
    mut v_a_4201_: *mut LeanObject,
    mut v_a_4202_: *mut LeanObject,
    mut v_a_4203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4204_: *mut LeanObject = core::ptr::null_mut();
    v_res_4204_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(
        v_e_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_,
        v_a_4200_, v_a_4201_, v_a_4202_,
    );
    lean_dec(v_a_4202_);
    lean_dec_ref(v_a_4201_);
    lean_dec(v_a_4200_);
    lean_dec_ref(v_a_4199_);
    lean_dec(v_a_4198_);
    lean_dec_ref(v_a_4197_);
    lean_dec(v_a_4196_);
    lean_dec_ref(v_a_4195_);
    lean_dec(v_a_4194_);
    lean_dec(v_a_4193_);
    return v_res_4204_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0() -> *mut LeanObject {
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    v___x_4205_ = lean_unsigned_to_nat(1);
    v___x_4206_ = lean_nat_to_int(v___x_4205_);
    return v___x_4206_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2() -> *mut LeanObject {
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    v___x_4208_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1;
    v___x_4209_ = l_Lean_stringToMessageData(v___x_4208_);
    return v___x_4209_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4() -> *mut LeanObject {
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    v___x_4211_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3;
    v___x_4212_ = l_Lean_stringToMessageData(v___x_4211_);
    return v___x_4212_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(
    mut v_e_4213_: *mut LeanObject,
    mut v_p_4214_: *mut LeanObject,
    mut v_a_4215_: *mut LeanObject,
    mut v_a_4216_: *mut LeanObject,
    mut v_a_4217_: *mut LeanObject,
    mut v_a_4218_: *mut LeanObject,
    mut v_a_4219_: *mut LeanObject,
    mut v_a_4220_: *mut LeanObject,
    mut v_a_4221_: *mut LeanObject,
    mut v_a_4222_: *mut LeanObject,
    mut v_a_4223_: *mut LeanObject,
    mut v_a_4224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4241_: u8 = 0;
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut v_a_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4251_: u8 = 0;
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4255_: u8 = 0;
    let mut v___x_4256_: u8 = 0;
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4271_: u8 = 0;
    let mut v_a_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4275_: u8 = 0;
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4279_: u8 = 0;
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4284_: u8 = 0;
    let mut v_val_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v___x_4289_: u8 = 0;
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: u8 = 0;
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4302_: u8 = 0;
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4306_: u8 = 0;
    let mut v_a_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4310_: u8 = 0;
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4321_: u8 = 0;
    let mut v_isSharedCheck_4322_: u8 = 0;
    let mut v_a_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4330_: u8 = 0;
    let mut v_a_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4256_ = 1;
                lean_inc_ref(v_e_4213_);
                v___x_4257_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(
                    v_e_4213_,
                    v___x_4256_,
                    v_a_4219_,
                    v_a_4220_,
                    v_a_4221_,
                    v_a_4222_,
                    v_a_4223_,
                    v_a_4224_,
                );
                if lean_obj_tag(v___x_4257_) == 0 {
                    v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
                    lean_inc(v_a_4258_);
                    lean_dec_ref_known(v___x_4257_, 1);
                    if lean_obj_tag(v_a_4258_) == 1 {
                        lean_dec_ref(v_e_4213_);
                        v_val_4259_ = lean_ctor_get(v_a_4258_, 0);
                        lean_inc(v_val_4259_);
                        lean_dec_ref_known(v_a_4258_, 1);
                        v_fst_4260_ = lean_ctor_get(v_val_4259_, 0);
                        lean_inc(v_fst_4260_);
                        v_snd_4261_ = lean_ctor_get(v_val_4259_, 1);
                        lean_inc(v_snd_4261_);
                        lean_dec(v_val_4259_);
                        lean_inc(v_a_4224_);
                        lean_inc_ref(v_a_4223_);
                        lean_inc(v_a_4222_);
                        lean_inc_ref(v_a_4221_);
                        lean_inc(v_a_4220_);
                        lean_inc_ref(v_a_4219_);
                        lean_inc(v_a_4218_);
                        lean_inc_ref(v_a_4217_);
                        lean_inc(v_a_4216_);
                        lean_inc(v_a_4215_);
                        v___x_4262_ = lean_grind_cutsat_mk_var(
                            v_snd_4261_,
                            v_a_4215_,
                            v_a_4216_,
                            v_a_4217_,
                            v_a_4218_,
                            v_a_4219_,
                            v_a_4220_,
                            v_a_4221_,
                            v_a_4222_,
                            v_a_4223_,
                            v_a_4224_,
                        );
                        if lean_obj_tag(v___x_4262_) == 0 {
                            v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
                            v_isSharedCheck_4271_ = (!lean_is_exclusive(v___x_4262_)) as u8;
                            if v_isSharedCheck_4271_ == 0 {
                                v___x_4265_ = v___x_4262_;
                                v_isShared_4266_ = v_isSharedCheck_4271_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_4263_);
                                lean_dec(v___x_4262_);
                                v___x_4265_ = lean_box(0);
                                v_isShared_4266_ = v_isSharedCheck_4271_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_4260_);
                            lean_dec_ref(v_p_4214_);
                            v_a_4272_ = lean_ctor_get(v___x_4262_, 0);
                            v_isSharedCheck_4279_ = (!lean_is_exclusive(v___x_4262_)) as u8;
                            if v_isSharedCheck_4279_ == 0 {
                                v___x_4274_ = v___x_4262_;
                                v_isShared_4275_ = v_isSharedCheck_4279_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_4272_);
                                lean_dec(v___x_4262_);
                                v___x_4274_ = lean_box(0);
                                v_isShared_4275_ = v_isSharedCheck_4279_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4258_);
                        lean_inc_ref(v_e_4213_);
                        v___x_4280_ = l_Lean_Meta_getIntValue_x3f(
                            v_e_4213_, v_a_4221_, v_a_4222_, v_a_4223_, v_a_4224_,
                        );
                        if lean_obj_tag(v___x_4280_) == 0 {
                            v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
                            v_isSharedCheck_4322_ = (!lean_is_exclusive(v___x_4280_)) as u8;
                            if v_isSharedCheck_4322_ == 0 {
                                v___x_4283_ = v___x_4280_;
                                v_isShared_4284_ = v_isSharedCheck_4322_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_4281_);
                                lean_dec(v___x_4280_);
                                v___x_4283_ = lean_box(0);
                                v_isShared_4284_ = v_isSharedCheck_4322_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_p_4214_);
                            lean_dec_ref(v_e_4213_);
                            v_a_4323_ = lean_ctor_get(v___x_4280_, 0);
                            v_isSharedCheck_4330_ = (!lean_is_exclusive(v___x_4280_)) as u8;
                            if v_isSharedCheck_4330_ == 0 {
                                v___x_4325_ = v___x_4280_;
                                v_isShared_4326_ = v_isSharedCheck_4330_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_4323_);
                                lean_dec(v___x_4280_);
                                v___x_4325_ = lean_box(0);
                                v_isShared_4326_ = v_isSharedCheck_4330_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_p_4214_);
                    lean_dec_ref(v_e_4213_);
                    v_a_4331_ = lean_ctor_get(v___x_4257_, 0);
                    v_isSharedCheck_4338_ = (!lean_is_exclusive(v___x_4257_)) as u8;
                    if v_isSharedCheck_4338_ == 0 {
                        v___x_4333_ = v___x_4257_;
                        v_isShared_4334_ = v_isSharedCheck_4338_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_4331_);
                        lean_dec(v___x_4257_);
                        v___x_4333_ = lean_box(0);
                        v_isShared_4334_ = v_isSharedCheck_4338_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_4236_);
                lean_inc_ref(v___y_4235_);
                lean_inc(v___y_4234_);
                lean_inc_ref(v___y_4233_);
                lean_inc(v___y_4232_);
                lean_inc_ref(v___y_4231_);
                lean_inc(v___y_4230_);
                lean_inc_ref(v___y_4229_);
                lean_inc(v___y_4228_);
                lean_inc(v___y_4227_);
                v___x_4237_ = lean_grind_cutsat_mk_var(
                    v_e_4213_,
                    v___y_4227_,
                    v___y_4228_,
                    v___y_4229_,
                    v___y_4230_,
                    v___y_4231_,
                    v___y_4232_,
                    v___y_4233_,
                    v___y_4234_,
                    v___y_4235_,
                    v___y_4236_,
                );
                if lean_obj_tag(v___x_4237_) == 0 {
                    v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
                    v_isSharedCheck_4247_ = (!lean_is_exclusive(v___x_4237_)) as u8;
                    if v_isSharedCheck_4247_ == 0 {
                        v___x_4240_ = v___x_4237_;
                        v_isShared_4241_ = v_isSharedCheck_4247_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4238_);
                        lean_dec(v___x_4237_);
                        v___x_4240_ = lean_box(0);
                        v_isShared_4241_ = v_isSharedCheck_4247_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_4214_);
                    v_a_4248_ = lean_ctor_get(v___x_4237_, 0);
                    v_isSharedCheck_4255_ = (!lean_is_exclusive(v___x_4237_)) as u8;
                    if v_isSharedCheck_4255_ == 0 {
                        v___x_4250_ = v___x_4237_;
                        v_isShared_4251_ = v_isSharedCheck_4255_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4248_);
                        lean_dec(v___x_4237_);
                        v___x_4250_ = lean_box(0);
                        v_isShared_4251_ = v_isSharedCheck_4255_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4242_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0,
                );
                v___x_4243_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4243_, 0, v___x_4242_);
                lean_ctor_set(v___x_4243_, 1, v_a_4238_);
                lean_ctor_set(v___x_4243_, 2, v_p_4214_);
                if v_isShared_4241_ == 0 {
                    lean_ctor_set(v___x_4240_, 0, v___x_4243_);
                    v___x_4245_ = v___x_4240_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4243_);
                    v___x_4245_ = v_reuseFailAlloc_4246_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4245_;
            }
            4 => {
                if v_isShared_4251_ == 0 {
                    v___x_4253_ = v___x_4250_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
                    v___x_4253_ = v_reuseFailAlloc_4254_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4253_;
            }
            6 => {
                v___x_4267_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4267_, 0, v_fst_4260_);
                lean_ctor_set(v___x_4267_, 1, v_a_4263_);
                lean_ctor_set(v___x_4267_, 2, v_p_4214_);
                if v_isShared_4266_ == 0 {
                    lean_ctor_set(v___x_4265_, 0, v___x_4267_);
                    v___x_4269_ = v___x_4265_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4270_, 0, v___x_4267_);
                    v___x_4269_ = v_reuseFailAlloc_4270_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4269_;
            }
            8 => {
                if v_isShared_4275_ == 0 {
                    v___x_4277_ = v___x_4274_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
                    v___x_4277_ = v_reuseFailAlloc_4278_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4277_;
            }
            10 => {
                if lean_obj_tag(v_a_4281_) == 1 {
                    v_val_4285_ = lean_ctor_get(v_a_4281_, 0);
                    v_isSharedCheck_4321_ = (!lean_is_exclusive(v_a_4281_)) as u8;
                    if v_isSharedCheck_4321_ == 0 {
                        v___x_4287_ = v_a_4281_;
                        v_isShared_4288_ = v_isSharedCheck_4321_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_val_4285_);
                        lean_dec(v_a_4281_);
                        v___x_4287_ = lean_box(0);
                        v_isShared_4288_ = v_isSharedCheck_4321_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4283_);
                    lean_dec(v_a_4281_);
                    v___y_4227_ = v_a_4215_;
                    v___y_4228_ = v_a_4216_;
                    v___y_4229_ = v_a_4217_;
                    v___y_4230_ = v_a_4218_;
                    v___y_4231_ = v_a_4219_;
                    v___y_4232_ = v_a_4220_;
                    v___y_4233_ = v_a_4221_;
                    v___y_4234_ = v_a_4222_;
                    v___y_4235_ = v_a_4223_;
                    v___y_4236_ = v_a_4224_;
                    state = 1;
                    continue;
                }
            }
            11 => {
                v___x_4289_ = l_Int_Linear_Poly_isZero(v_p_4214_);
                if v___x_4289_ == 0 {
                    lean_del_object(v___x_4287_);
                    lean_dec(v_val_4285_);
                    lean_del_object(v___x_4283_);
                    v___x_4290_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4219_);
                    if lean_obj_tag(v___x_4290_) == 0 {
                        v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
                        lean_inc(v_a_4291_);
                        lean_dec_ref_known(v___x_4290_, 1);
                        v___x_4292_ = (lean_unbox(v_a_4291_) as u8);
                        lean_dec(v_a_4291_);
                        if v___x_4292_ == 0 {
                            v___y_4227_ = v_a_4215_;
                            v___y_4228_ = v_a_4216_;
                            v___y_4229_ = v_a_4217_;
                            v___y_4230_ = v_a_4218_;
                            v___y_4231_ = v_a_4219_;
                            v___y_4232_ = v_a_4220_;
                            v___y_4233_ = v_a_4221_;
                            v___y_4234_ = v_a_4222_;
                            v___y_4235_ = v_a_4223_;
                            v___y_4236_ = v_a_4224_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4293_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once
                                ),
                                _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2,
                            );
                            lean_inc_ref(v_e_4213_);
                            v___x_4294_ = l_Lean_indentExpr(v_e_4213_);
                            v___x_4295_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4295_, 0, v___x_4293_);
                            lean_ctor_set(v___x_4295_, 1, v___x_4294_);
                            v___x_4296_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once
                                ),
                                _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4,
                            );
                            v___x_4297_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4297_, 0, v___x_4295_);
                            lean_ctor_set(v___x_4297_, 1, v___x_4296_);
                            v___x_4298_ = l_Lean_Meta_Sym_reportIssue(
                                v___x_4297_,
                                v_a_4219_,
                                v_a_4220_,
                                v_a_4221_,
                                v_a_4222_,
                                v_a_4223_,
                                v_a_4224_,
                            );
                            if lean_obj_tag(v___x_4298_) == 0 {
                                lean_dec_ref_known(v___x_4298_, 1);
                                v___y_4227_ = v_a_4215_;
                                v___y_4228_ = v_a_4216_;
                                v___y_4229_ = v_a_4217_;
                                v___y_4230_ = v_a_4218_;
                                v___y_4231_ = v_a_4219_;
                                v___y_4232_ = v_a_4220_;
                                v___y_4233_ = v_a_4221_;
                                v___y_4234_ = v_a_4222_;
                                v___y_4235_ = v_a_4223_;
                                v___y_4236_ = v_a_4224_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_p_4214_);
                                lean_dec_ref(v_e_4213_);
                                v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
                                v_isSharedCheck_4306_ = (!lean_is_exclusive(v___x_4298_)) as u8;
                                if v_isSharedCheck_4306_ == 0 {
                                    v___x_4301_ = v___x_4298_;
                                    v_isShared_4302_ = v_isSharedCheck_4306_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_4299_);
                                    lean_dec(v___x_4298_);
                                    v___x_4301_ = lean_box(0);
                                    v_isShared_4302_ = v_isSharedCheck_4306_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_p_4214_);
                        lean_dec_ref(v_e_4213_);
                        v_a_4307_ = lean_ctor_get(v___x_4290_, 0);
                        v_isSharedCheck_4314_ = (!lean_is_exclusive(v___x_4290_)) as u8;
                        if v_isSharedCheck_4314_ == 0 {
                            v___x_4309_ = v___x_4290_;
                            v_isShared_4310_ = v_isSharedCheck_4314_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_4307_);
                            lean_dec(v___x_4290_);
                            v___x_4309_ = lean_box(0);
                            v_isShared_4310_ = v_isSharedCheck_4314_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_p_4214_);
                    lean_dec_ref(v_e_4213_);
                    if v_isShared_4288_ == 0 {
                        lean_ctor_set_tag(v___x_4287_, 0);
                        v___x_4316_ = v___x_4287_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_val_4285_);
                        v___x_4316_ = v_reuseFailAlloc_4320_;
                        state = 16;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_4302_ == 0 {
                    v___x_4304_ = v___x_4301_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
                    v___x_4304_ = v_reuseFailAlloc_4305_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4304_;
            }
            14 => {
                if v_isShared_4310_ == 0 {
                    v___x_4312_ = v___x_4309_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
                    v___x_4312_ = v_reuseFailAlloc_4313_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4312_;
            }
            16 => {
                if v_isShared_4284_ == 0 {
                    lean_ctor_set(v___x_4283_, 0, v___x_4316_);
                    v___x_4318_ = v___x_4283_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4316_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4318_;
            }
            18 => {
                if v_isShared_4326_ == 0 {
                    v___x_4328_ = v___x_4325_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
                    v___x_4328_ = v_reuseFailAlloc_4329_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4328_;
            }
            20 => {
                if v_isShared_4334_ == 0 {
                    v___x_4336_ = v___x_4333_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
                    v___x_4336_ = v_reuseFailAlloc_4337_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(
    mut v_e_4339_: *mut LeanObject,
    mut v_p_4340_: *mut LeanObject,
    mut v_a_4341_: *mut LeanObject,
    mut v_a_4342_: *mut LeanObject,
    mut v_a_4343_: *mut LeanObject,
    mut v_a_4344_: *mut LeanObject,
    mut v_a_4345_: *mut LeanObject,
    mut v_a_4346_: *mut LeanObject,
    mut v_a_4347_: *mut LeanObject,
    mut v_a_4348_: *mut LeanObject,
    mut v_a_4349_: *mut LeanObject,
    mut v_a_4350_: *mut LeanObject,
    mut v_a_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4352_: *mut LeanObject = core::ptr::null_mut();
    v_res_4352_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(
        v_e_4339_, v_p_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_,
        v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_,
    );
    lean_dec(v_a_4350_);
    lean_dec_ref(v_a_4349_);
    lean_dec(v_a_4348_);
    lean_dec_ref(v_a_4347_);
    lean_dec(v_a_4346_);
    lean_dec_ref(v_a_4345_);
    lean_dec(v_a_4344_);
    lean_dec_ref(v_a_4343_);
    lean_dec(v_a_4342_);
    lean_dec(v_a_4341_);
    return v_res_4352_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(
    mut v_e_4353_: *mut LeanObject,
    mut v_p_4354_: *mut LeanObject,
    mut v_a_4355_: *mut LeanObject,
    mut v_a_4356_: *mut LeanObject,
    mut v_a_4357_: *mut LeanObject,
    mut v_a_4358_: *mut LeanObject,
    mut v_a_4359_: *mut LeanObject,
    mut v_a_4360_: *mut LeanObject,
    mut v_a_4361_: *mut LeanObject,
    mut v_a_4362_: *mut LeanObject,
    mut v_a_4363_: *mut LeanObject,
    mut v_a_4364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4366_: u8 = 0;
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4379_: u8 = 0;
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4366_ = 1;
                lean_inc_ref(v_e_4353_);
                v___x_4367_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(
                    v_e_4353_,
                    v___x_4366_,
                    v_a_4359_,
                    v_a_4360_,
                    v_a_4361_,
                    v_a_4362_,
                    v_a_4363_,
                    v_a_4364_,
                );
                if lean_obj_tag(v___x_4367_) == 0 {
                    v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
                    lean_inc(v_a_4368_);
                    lean_dec_ref_known(v___x_4367_, 1);
                    if lean_obj_tag(v_a_4368_) == 1 {
                        lean_dec_ref(v_e_4353_);
                        v_val_4369_ = lean_ctor_get(v_a_4368_, 0);
                        lean_inc(v_val_4369_);
                        lean_dec_ref_known(v_a_4368_, 1);
                        v_fst_4370_ = lean_ctor_get(v_val_4369_, 0);
                        lean_inc(v_fst_4370_);
                        v_snd_4371_ = lean_ctor_get(v_val_4369_, 1);
                        lean_inc(v_snd_4371_);
                        lean_dec(v_val_4369_);
                        v___x_4372_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(
                            v_snd_4371_,
                            v_p_4354_,
                            v_a_4355_,
                            v_a_4356_,
                            v_a_4357_,
                            v_a_4358_,
                            v_a_4359_,
                            v_a_4360_,
                            v_a_4361_,
                            v_a_4362_,
                            v_a_4363_,
                            v_a_4364_,
                        );
                        if lean_obj_tag(v___x_4372_) == 0 {
                            v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
                            lean_inc(v_a_4373_);
                            lean_dec_ref_known(v___x_4372_, 1);
                            v_e_4353_ = v_fst_4370_;
                            v_p_4354_ = v_a_4373_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_fst_4370_);
                            return v___x_4372_;
                        }
                    } else {
                        lean_dec(v_a_4368_);
                        v___x_4375_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(
                            v_e_4353_, v_p_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_,
                            v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_,
                        );
                        return v___x_4375_;
                    }
                } else {
                    lean_dec_ref(v_p_4354_);
                    lean_dec_ref(v_e_4353_);
                    v_a_4376_ = lean_ctor_get(v___x_4367_, 0);
                    v_isSharedCheck_4383_ = (!lean_is_exclusive(v___x_4367_)) as u8;
                    if v_isSharedCheck_4383_ == 0 {
                        v___x_4378_ = v___x_4367_;
                        v_isShared_4379_ = v_isSharedCheck_4383_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4376_);
                        lean_dec(v___x_4367_);
                        v___x_4378_ = lean_box(0);
                        v_isShared_4379_ = v_isSharedCheck_4383_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4379_ == 0 {
                    v___x_4381_ = v___x_4378_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
                    v___x_4381_ = v_reuseFailAlloc_4382_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(
    mut v_e_4384_: *mut LeanObject,
    mut v_p_4385_: *mut LeanObject,
    mut v_a_4386_: *mut LeanObject,
    mut v_a_4387_: *mut LeanObject,
    mut v_a_4388_: *mut LeanObject,
    mut v_a_4389_: *mut LeanObject,
    mut v_a_4390_: *mut LeanObject,
    mut v_a_4391_: *mut LeanObject,
    mut v_a_4392_: *mut LeanObject,
    mut v_a_4393_: *mut LeanObject,
    mut v_a_4394_: *mut LeanObject,
    mut v_a_4395_: *mut LeanObject,
    mut v_a_4396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4397_: *mut LeanObject = core::ptr::null_mut();
    v_res_4397_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_4384_, v_p_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_);
    lean_dec(v_a_4395_);
    lean_dec_ref(v_a_4394_);
    lean_dec(v_a_4393_);
    lean_dec_ref(v_a_4392_);
    lean_dec(v_a_4391_);
    lean_dec_ref(v_a_4390_);
    lean_dec(v_a_4389_);
    lean_dec_ref(v_a_4388_);
    lean_dec(v_a_4387_);
    lean_dec(v_a_4386_);
    return v_res_4397_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0() -> *mut LeanObject {
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    v___x_4398_ = lean_unsigned_to_nat(0);
    v___x_4399_ = lean_nat_to_int(v___x_4398_);
    return v___x_4399_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1() -> *mut LeanObject {
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    v___x_4400_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0,
    );
    v___x_4401_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4401_, 0, v___x_4400_);
    return v___x_4401_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_toPoly(
    mut v_e_4402_: *mut LeanObject,
    mut v_a_4403_: *mut LeanObject,
    mut v_a_4404_: *mut LeanObject,
    mut v_a_4405_: *mut LeanObject,
    mut v_a_4406_: *mut LeanObject,
    mut v_a_4407_: *mut LeanObject,
    mut v_a_4408_: *mut LeanObject,
    mut v_a_4409_: *mut LeanObject,
    mut v_a_4410_: *mut LeanObject,
    mut v_a_4411_: *mut LeanObject,
    mut v_a_4412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4414_: u8 = 0;
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4429_: u8 = 0;
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4414_ = 1;
                lean_inc_ref(v_e_4402_);
                v___x_4415_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(
                    v_e_4402_,
                    v___x_4414_,
                    v_a_4407_,
                    v_a_4408_,
                    v_a_4409_,
                    v_a_4410_,
                    v_a_4411_,
                    v_a_4412_,
                );
                if lean_obj_tag(v___x_4415_) == 0 {
                    v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
                    lean_inc(v_a_4416_);
                    lean_dec_ref_known(v___x_4415_, 1);
                    if lean_obj_tag(v_a_4416_) == 1 {
                        lean_dec_ref(v_e_4402_);
                        v_val_4417_ = lean_ctor_get(v_a_4416_, 0);
                        lean_inc(v_val_4417_);
                        lean_dec_ref_known(v_a_4416_, 1);
                        v_fst_4418_ = lean_ctor_get(v_val_4417_, 0);
                        lean_inc(v_fst_4418_);
                        v_snd_4419_ = lean_ctor_get(v_val_4417_, 1);
                        lean_inc(v_snd_4419_);
                        lean_dec(v_val_4417_);
                        v___x_4420_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1,
                        );
                        v___x_4421_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(
                            v_snd_4419_,
                            v___x_4420_,
                            v_a_4403_,
                            v_a_4404_,
                            v_a_4405_,
                            v_a_4406_,
                            v_a_4407_,
                            v_a_4408_,
                            v_a_4409_,
                            v_a_4410_,
                            v_a_4411_,
                            v_a_4412_,
                        );
                        if lean_obj_tag(v___x_4421_) == 0 {
                            v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
                            lean_inc(v_a_4422_);
                            lean_dec_ref_known(v___x_4421_, 1);
                            v___x_4423_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_4418_, v_a_4422_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_);
                            return v___x_4423_;
                        } else {
                            lean_dec(v_fst_4418_);
                            return v___x_4421_;
                        }
                    } else {
                        lean_dec(v_a_4416_);
                        v___x_4424_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1,
                        );
                        v___x_4425_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(
                            v_e_4402_,
                            v___x_4424_,
                            v_a_4403_,
                            v_a_4404_,
                            v_a_4405_,
                            v_a_4406_,
                            v_a_4407_,
                            v_a_4408_,
                            v_a_4409_,
                            v_a_4410_,
                            v_a_4411_,
                            v_a_4412_,
                        );
                        return v___x_4425_;
                    }
                } else {
                    lean_dec_ref(v_e_4402_);
                    v_a_4426_ = lean_ctor_get(v___x_4415_, 0);
                    v_isSharedCheck_4433_ = (!lean_is_exclusive(v___x_4415_)) as u8;
                    if v_isSharedCheck_4433_ == 0 {
                        v___x_4428_ = v___x_4415_;
                        v_isShared_4429_ = v_isSharedCheck_4433_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4426_);
                        lean_dec(v___x_4415_);
                        v___x_4428_ = lean_box(0);
                        v_isShared_4429_ = v_isSharedCheck_4433_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4429_ == 0 {
                    v___x_4431_ = v___x_4428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
                    v___x_4431_ = v_reuseFailAlloc_4432_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4431_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(
    mut v_e_4434_: *mut LeanObject,
    mut v_a_4435_: *mut LeanObject,
    mut v_a_4436_: *mut LeanObject,
    mut v_a_4437_: *mut LeanObject,
    mut v_a_4438_: *mut LeanObject,
    mut v_a_4439_: *mut LeanObject,
    mut v_a_4440_: *mut LeanObject,
    mut v_a_4441_: *mut LeanObject,
    mut v_a_4442_: *mut LeanObject,
    mut v_a_4443_: *mut LeanObject,
    mut v_a_4444_: *mut LeanObject,
    mut v_a_4445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4446_: *mut LeanObject = core::ptr::null_mut();
    v_res_4446_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(
        v_e_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_,
        v_a_4442_, v_a_4443_, v_a_4444_,
    );
    lean_dec(v_a_4444_);
    lean_dec_ref(v_a_4443_);
    lean_dec(v_a_4442_);
    lean_dec_ref(v_a_4441_);
    lean_dec(v_a_4440_);
    lean_dec_ref(v_a_4439_);
    lean_dec(v_a_4438_);
    lean_dec_ref(v_a_4437_);
    lean_dec(v_a_4436_);
    lean_dec(v_a_4435_);
    return v_res_4446_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_IntInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
}

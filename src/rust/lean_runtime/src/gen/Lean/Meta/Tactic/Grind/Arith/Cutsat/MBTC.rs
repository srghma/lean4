// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.MBTC
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.MBTC Lean.Meta.Tactic.Grind.Arith.ModelUtil Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_ofInt, l_instDecidableEqRat_decEq};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_getAppFn,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Int_mkType, l_Lean_Nat_mkType,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_getIntValue_x3f;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Model::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model,
    l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util,
    l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::ModelUtil::{
    initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil, l_Lean_Meta_Grind_Arith_isInterpretedTerm,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MBTC::{
    initialize_Lean_Meta_Tactic_Grind_MBTC, l_Lean_Meta_Grind_mbtc,
    runtime_initialize_Lean_Meta_Tactic_Grind_MBTC,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_ParentSet_elems, l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg,
    l_Lean_Meta_Grind_alreadyInternalized___redArg, l_Lean_Meta_Grind_getParents___redArg,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_sub, lean_usize_to_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_nat_add,
    lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__1_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__2_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__1_value) as *mut LeanObject,5779414593499529281 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__2_value) as *mut LeanObject,7063772860359172143 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__4_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 110, 115, 116, 78, 97, 116, 67, 97, 115, 116, 73, 110, 116, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__4_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__4_value) as *mut LeanObject,14240220390202531956 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__5_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0_value) as *mut LeanObject,13744984671752750173 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1_value) as *mut LeanObject,9682224670061807480 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3_value) as *mut LeanObject,11858238400308895562 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4_value) as *mut LeanObject,6100819061652633370 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6_value) as *mut LeanObject,2929883540436775422 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7_value) as *mut LeanObject,1611444129324655608 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0_value) as *mut LeanObject,8347582161988589016 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1_value) as *mut LeanObject,7316284823769321069 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 118, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 118, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3_value) as *mut LeanObject,4493959381811283967 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4_value) as *mut LeanObject,1297950917268934889 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6_value) as *mut LeanObject,17878876274162330439 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7_value) as *mut LeanObject,11833570877100518198 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3_value) as *mut LeanObject;
pub unsafe fn l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1(
    mut v_a_756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    v___x_757_ = l_Rat_ofInt(v_a_756_);
    return v___x_757_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg(
    mut v_as_x27_769_: *mut LeanObject,
    mut v_b_770_: *mut LeanObject,
    mut v___y_771_: *mut LeanObject,
    mut v___y_772_: *mut LeanObject,
    mut v___y_773_: *mut LeanObject,
    mut v___y_774_: *mut LeanObject,
    mut v___y_775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: u8 = 0;
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: u8 = 0;
    let mut v_arg_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u8 = 0;
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u8 = 0;
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: u8 = 0;
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_811_: u8 = 0;
    let mut v_a_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_815_: u8 = 0;
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_769_) == 0 {
                    v___x_777_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_777_, 0, v_b_770_);
                    return v___x_777_;
                } else {
                    lean_dec_ref(v_b_770_);
                    v_head_778_ = lean_ctor_get(v_as_x27_769_, 0);
                    v_tail_779_ = lean_ctor_get(v_as_x27_769_, 1);
                    v___x_780_ = lean_box(0);
                    v___x_781_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__0;
                    lean_inc(v_head_778_);
                    v___x_782_ = l_Lean_Expr_cleanupAnnotations(v_head_778_);
                    v___x_783_ = l_Lean_Expr_isApp(v___x_782_);
                    if v___x_783_ == 0 {
                        lean_dec_ref(v___x_782_);
                        v_as_x27_769_ = v_tail_779_;
                        v_b_770_ = v___x_781_;
                        state = 0;
                        continue;
                    } else {
                        v___x_785_ = l_Lean_Expr_appFnCleanup___redArg(v___x_782_);
                        v___x_786_ = l_Lean_Expr_isApp(v___x_785_);
                        if v___x_786_ == 0 {
                            lean_dec_ref(v___x_785_);
                            v_as_x27_769_ = v_tail_779_;
                            v_b_770_ = v___x_781_;
                            state = 0;
                            continue;
                        } else {
                            v_arg_788_ = lean_ctor_get(v___x_785_, 1);
                            lean_inc_ref(v_arg_788_);
                            v___x_789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_785_);
                            v___x_790_ = l_Lean_Expr_isApp(v___x_789_);
                            if v___x_790_ == 0 {
                                lean_dec_ref(v___x_789_);
                                lean_dec_ref(v_arg_788_);
                                v_as_x27_769_ = v_tail_779_;
                                v_b_770_ = v___x_781_;
                                state = 0;
                                continue;
                            } else {
                                v___x_792_ = l_Lean_Expr_appFnCleanup___redArg(v___x_789_);
                                v___x_793_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3;
                                v___x_794_ = l_Lean_Expr_isConstOf(v___x_792_, v___x_793_);
                                lean_dec_ref(v___x_792_);
                                if v___x_794_ == 0 {
                                    lean_dec_ref(v_arg_788_);
                                    v_as_x27_769_ = v_tail_779_;
                                    v_b_770_ = v___x_781_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_796_ = l_Lean_Expr_cleanupAnnotations(v_arg_788_);
                                    v___x_797_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__5;
                                    v___x_798_ = l_Lean_Expr_isConstOf(v___x_796_, v___x_797_);
                                    lean_dec_ref(v___x_796_);
                                    if v___x_798_ == 0 {
                                        v_as_x27_769_ = v_tail_779_;
                                        v_b_770_ = v___x_781_;
                                        state = 0;
                                        continue;
                                    } else {
                                        v___x_800_ = lean_st_ref_get(v___y_771_);
                                        lean_inc(v_head_778_);
                                        v___x_801_ =
                                            l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(
                                                v___x_800_,
                                                v_head_778_,
                                                v___y_772_,
                                                v___y_773_,
                                                v___y_774_,
                                                v___y_775_,
                                            );
                                        lean_dec(v___x_800_);
                                        if lean_obj_tag(v___x_801_) == 0 {
                                            v_a_802_ = lean_ctor_get(v___x_801_, 0);
                                            v_isSharedCheck_811_ =
                                                (!lean_is_exclusive(v___x_801_)) as u8;
                                            if v_isSharedCheck_811_ == 0 {
                                                v___x_804_ = v___x_801_;
                                                v_isShared_805_ = v_isSharedCheck_811_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc(v_a_802_);
                                                lean_dec(v___x_801_);
                                                v___x_804_ = lean_box(0);
                                                v_isShared_805_ = v_isSharedCheck_811_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v_a_812_ = lean_ctor_get(v___x_801_, 0);
                                            v_isSharedCheck_819_ =
                                                (!lean_is_exclusive(v___x_801_)) as u8;
                                            if v_isSharedCheck_819_ == 0 {
                                                v___x_814_ = v___x_801_;
                                                v_isShared_815_ = v_isSharedCheck_819_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_812_);
                                                lean_dec(v___x_801_);
                                                v___x_814_ = lean_box(0);
                                                v_isShared_815_ = v_isSharedCheck_819_;
                                                state = 3;
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
            1 => {
                v___x_806_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_806_, 0, v_a_802_);
                v___x_807_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_807_, 0, v___x_806_);
                lean_ctor_set(v___x_807_, 1, v___x_780_);
                if v_isShared_805_ == 0 {
                    lean_ctor_set(v___x_804_, 0, v___x_807_);
                    v___x_809_ = v___x_804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
                    v___x_809_ = v_reuseFailAlloc_810_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_809_;
            }
            3 => {
                if v_isShared_815_ == 0 {
                    v___x_817_ = v___x_814_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
                    v___x_817_ = v_reuseFailAlloc_818_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___boxed(
    mut v_as_x27_820_: *mut LeanObject,
    mut v_b_821_: *mut LeanObject,
    mut v___y_822_: *mut LeanObject,
    mut v___y_823_: *mut LeanObject,
    mut v___y_824_: *mut LeanObject,
    mut v___y_825_: *mut LeanObject,
    mut v___y_826_: *mut LeanObject,
    mut v___y_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_828_: *mut LeanObject = core::ptr::null_mut();
    v_res_828_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg(v_as_x27_820_, v_b_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
    lean_dec(v___y_826_);
    lean_dec_ref(v___y_825_);
    lean_dec(v___y_824_);
    lean_dec_ref(v___y_823_);
    lean_dec(v___y_822_);
    lean_dec(v_as_x27_820_);
    return v_res_828_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg(
    mut v_keys_829_: *mut LeanObject,
    mut v_vals_830_: *mut LeanObject,
    mut v_i_831_: *mut LeanObject,
    mut v_k_832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: u8 = 0;
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: u8 = 0;
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_833_ = lean_array_get_size(v_keys_829_);
                v___x_834_ = lean_nat_dec_lt(v_i_831_, v___x_833_);
                if v___x_834_ == 0 {
                    lean_dec(v_i_831_);
                    v___x_835_ = lean_box(0);
                    return v___x_835_;
                } else {
                    v_k_x27_836_ = lean_array_fget_borrowed(v_keys_829_, v_i_831_);
                    v___x_837_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_832_,
                            v_k_x27_836_,
                        );
                    if v___x_837_ == 0 {
                        v___x_838_ = lean_unsigned_to_nat(1);
                        v___x_839_ = lean_nat_add(v_i_831_, v___x_838_);
                        lean_dec(v_i_831_);
                        v_i_831_ = v___x_839_;
                        state = 0;
                        continue;
                    } else {
                        v___x_841_ = lean_array_fget_borrowed(v_vals_830_, v_i_831_);
                        lean_dec(v_i_831_);
                        lean_inc(v___x_841_);
                        v___x_842_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_842_, 0, v___x_841_);
                        return v___x_842_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_keys_843_: *mut LeanObject,
    mut v_vals_844_: *mut LeanObject,
    mut v_i_845_: *mut LeanObject,
    mut v_k_846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_847_: *mut LeanObject = core::ptr::null_mut();
    v_res_847_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg(v_keys_843_, v_vals_844_, v_i_845_, v_k_846_);
    lean_dec_ref(v_k_846_);
    lean_dec_ref(v_vals_844_);
    lean_dec_ref(v_keys_843_);
    return v_res_847_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_848_: usize = 0;
    let mut v___x_849_: usize = 0;
    let mut v___x_850_: usize = 0;
    v___x_848_ = 5usize;
    v___x_849_ = 1usize;
    v___x_850_ = lean_usize_shift_left(v___x_849_, v___x_848_);
    return v___x_850_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_851_: usize = 0;
    let mut v___x_852_: usize = 0;
    let mut v___x_853_: usize = 0;
    v___x_851_ = 1usize;
    v___x_852_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_853_ = lean_usize_sub(v___x_852_, v___x_851_);
    return v___x_853_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg(
    mut v_x_854_: *mut LeanObject,
    mut v_x_855_: usize,
    mut v_x_856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: usize = 0;
    let mut v___x_860_: usize = 0;
    let mut v___x_861_: usize = 0;
    let mut v_j_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: u8 = 0;
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: usize = 0;
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_854_) == 0 {
                    v_es_857_ = lean_ctor_get(v_x_854_, 0);
                    v___x_858_ = lean_box(2);
                    v___x_859_ = 5usize;
                    v___x_860_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_861_ = lean_usize_land(v_x_855_, v___x_860_);
                    v_j_862_ = lean_usize_to_nat(v___x_861_);
                    v___x_863_ = lean_array_get_borrowed(v___x_858_, v_es_857_, v_j_862_);
                    lean_dec(v_j_862_);
                    match lean_obj_tag(v___x_863_) {
                        0 => {
                            v_key_864_ = lean_ctor_get(v___x_863_, 0);
                            v_val_865_ = lean_ctor_get(v___x_863_, 1);
                            v___x_866_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_856_, v_key_864_);
                            if v___x_866_ == 0 {
                                v___x_867_ = lean_box(0);
                                return v___x_867_;
                            } else {
                                lean_inc(v_val_865_);
                                v___x_868_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_868_, 0, v_val_865_);
                                return v___x_868_;
                            }
                        }
                        1 => {
                            v_node_869_ = lean_ctor_get(v___x_863_, 0);
                            v___x_870_ = lean_usize_shift_right(v_x_855_, v___x_859_);
                            v_x_854_ = v_node_869_;
                            v_x_855_ = v___x_870_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_872_ = lean_box(0);
                            return v___x_872_;
                        }
                    }
                } else {
                    v_ks_873_ = lean_ctor_get(v_x_854_, 0);
                    v_vs_874_ = lean_ctor_get(v_x_854_, 1);
                    v___x_875_ = lean_unsigned_to_nat(0);
                    v___x_876_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg(v_ks_873_, v_vs_874_, v___x_875_, v_x_856_);
                    return v___x_876_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_877_: *mut LeanObject,
    mut v_x_878_: *mut LeanObject,
    mut v_x_879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_52166__boxed_880_: usize = 0;
    let mut v_res_881_: *mut LeanObject = core::ptr::null_mut();
    v_x_52166__boxed_880_ = lean_unbox_usize(v_x_878_);
    lean_dec(v_x_878_);
    v_res_881_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg(v_x_877_, v_x_52166__boxed_880_, v_x_879_);
    lean_dec_ref(v_x_879_);
    lean_dec_ref(v_x_877_);
    return v_res_881_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(
    mut v_x_882_: *mut LeanObject,
    mut v_x_883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_884_: u64 = 0;
    let mut v___x_885_: usize = 0;
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    v___x_884_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_883_);
    v___x_885_ = lean_uint64_to_usize(v___x_884_);
    v___x_886_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg(v_x_882_, v___x_885_, v_x_883_);
    return v___x_886_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg___boxed(
    mut v_x_887_: *mut LeanObject,
    mut v_x_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_889_: *mut LeanObject = core::ptr::null_mut();
    v_res_889_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_x_887_, v_x_888_);
    lean_dec_ref(v_x_888_);
    lean_dec_ref(v_x_887_);
    return v_res_889_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(
    mut v_e_890_: *mut LeanObject,
    mut v_a_891_: *mut LeanObject,
    mut v_a_892_: *mut LeanObject,
    mut v_a_893_: *mut LeanObject,
    mut v_a_894_: *mut LeanObject,
    mut v_a_895_: *mut LeanObject,
    mut v_a_896_: *mut LeanObject,
    mut v_a_897_: *mut LeanObject,
    mut v_a_898_: *mut LeanObject,
    mut v_a_899_: *mut LeanObject,
    mut v_a_900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eToInt_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_925_: u8 = 0;
    let mut v_val_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_937_: u8 = 0;
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: u8 = 0;
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_952_: u8 = 0;
    let mut v_isSharedCheck_953_: u8 = 0;
    let mut v_a_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_957_: u8 = 0;
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_961_: u8 = 0;
    let mut v_a_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_965_: u8 = 0;
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_969_: u8 = 0;
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_978_: u8 = 0;
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: u8 = 0;
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: u8 = 0;
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_999_: u8 = 0;
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1008_: u8 = 0;
    let mut v_fst_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1014_: u8 = 0;
    let mut v_a_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1018_: u8 = 0;
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1022_: u8 = 0;
    let mut v_a_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1026_: u8 = 0;
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1030_: u8 = 0;
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1035_: u8 = 0;
    let mut v_a_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1039_: u8 = 0;
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_970_ = lean_st_ref_get(v_a_891_);
                lean_inc_ref(v_e_890_);
                v___x_971_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(
                    v___x_970_, v_e_890_, v_a_897_, v_a_898_, v_a_899_, v_a_900_,
                );
                lean_dec(v___x_970_);
                if lean_obj_tag(v___x_971_) == 0 {
                    v_a_972_ = lean_ctor_get(v___x_971_, 0);
                    lean_inc(v_a_972_);
                    lean_dec_ref_known(v___x_971_, 1);
                    if lean_obj_tag(v_a_972_) == 1 {
                        lean_dec_ref(v_e_890_);
                        v_val_973_ = lean_ctor_get(v_a_972_, 0);
                        lean_inc(v_val_973_);
                        lean_dec_ref_known(v_a_972_, 1);
                        v_val_903_ = v_val_973_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_972_);
                        lean_inc(v_a_900_);
                        lean_inc_ref(v_a_899_);
                        lean_inc(v_a_898_);
                        lean_inc_ref(v_a_897_);
                        lean_inc_ref(v_e_890_);
                        v___x_974_ =
                            lean_infer_type(v_e_890_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
                        if lean_obj_tag(v___x_974_) == 0 {
                            v_a_975_ = lean_ctor_get(v___x_974_, 0);
                            v_isSharedCheck_1035_ = (!lean_is_exclusive(v___x_974_)) as u8;
                            if v_isSharedCheck_1035_ == 0 {
                                v___x_977_ = v___x_974_;
                                v_isShared_978_ = v_isSharedCheck_1035_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_975_);
                                lean_dec(v___x_974_);
                                v___x_977_ = lean_box(0);
                                v_isShared_978_ = v_isSharedCheck_1035_;
                                state = 14;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_e_890_);
                            v_a_1036_ = lean_ctor_get(v___x_974_, 0);
                            v_isSharedCheck_1043_ = (!lean_is_exclusive(v___x_974_)) as u8;
                            if v_isSharedCheck_1043_ == 0 {
                                v___x_1038_ = v___x_974_;
                                v_isShared_1039_ = v_isSharedCheck_1043_;
                                state = 24;
                                continue;
                            } else {
                                lean_inc(v_a_1036_);
                                lean_dec(v___x_974_);
                                v___x_1038_ = lean_box(0);
                                v_isShared_1039_ = v_isSharedCheck_1043_;
                                state = 24;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_890_);
                    return v___x_971_;
                }
            }
            1 => {
                v___x_904_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_904_, 0, v_val_903_);
                v___x_905_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_905_, 0, v___x_904_);
                return v___x_905_;
            }
            2 => {
                v___x_907_ = lean_box(0);
                v___x_908_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_908_, 0, v___x_907_);
                return v___x_908_;
            }
            3 => {
                v___x_915_ =
                    l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_910_, v___y_913_);
                if lean_obj_tag(v___x_915_) == 0 {
                    v_a_916_ = lean_ctor_get(v___x_915_, 0);
                    lean_inc(v_a_916_);
                    lean_dec_ref_known(v___x_915_, 1);
                    v_toIntTermMap_917_ = lean_ctor_get(v_a_916_, 20);
                    lean_inc_ref(v_toIntTermMap_917_);
                    lean_dec(v_a_916_);
                    v___x_918_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_toIntTermMap_917_, v_e_890_);
                    lean_dec_ref(v_e_890_);
                    lean_dec_ref(v_toIntTermMap_917_);
                    if lean_obj_tag(v___x_918_) == 1 {
                        v_val_919_ = lean_ctor_get(v___x_918_, 0);
                        lean_inc(v_val_919_);
                        lean_dec_ref_known(v___x_918_, 1);
                        v_eToInt_920_ = lean_ctor_get(v_val_919_, 0);
                        lean_inc_ref_n(v_eToInt_920_, 2);
                        lean_dec(v_val_919_);
                        v___x_921_ = l_Lean_Meta_getIntValue_x3f(
                            v_eToInt_920_,
                            v___y_911_,
                            v___y_912_,
                            v___y_913_,
                            v___y_914_,
                        );
                        if lean_obj_tag(v___x_921_) == 0 {
                            v_a_922_ = lean_ctor_get(v___x_921_, 0);
                            v_isSharedCheck_953_ = (!lean_is_exclusive(v___x_921_)) as u8;
                            if v_isSharedCheck_953_ == 0 {
                                v___x_924_ = v___x_921_;
                                v_isShared_925_ = v_isSharedCheck_953_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_922_);
                                lean_dec(v___x_921_);
                                v___x_924_ = lean_box(0);
                                v_isShared_925_ = v_isSharedCheck_953_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_eToInt_920_);
                            v_a_954_ = lean_ctor_get(v___x_921_, 0);
                            v_isSharedCheck_961_ = (!lean_is_exclusive(v___x_921_)) as u8;
                            if v_isSharedCheck_961_ == 0 {
                                v___x_956_ = v___x_921_;
                                v_isShared_957_ = v_isSharedCheck_961_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_954_);
                                lean_dec(v___x_921_);
                                v___x_956_ = lean_box(0);
                                v_isShared_957_ = v_isSharedCheck_961_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_918_);
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_890_);
                    v_a_962_ = lean_ctor_get(v___x_915_, 0);
                    v_isSharedCheck_969_ = (!lean_is_exclusive(v___x_915_)) as u8;
                    if v_isSharedCheck_969_ == 0 {
                        v___x_964_ = v___x_915_;
                        v_isShared_965_ = v_isSharedCheck_969_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_962_);
                        lean_dec(v___x_915_);
                        v___x_964_ = lean_box(0);
                        v_isShared_965_ = v_isSharedCheck_969_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_a_922_) == 1 {
                    lean_dec_ref(v_eToInt_920_);
                    v_val_926_ = lean_ctor_get(v_a_922_, 0);
                    v_isSharedCheck_937_ = (!lean_is_exclusive(v_a_922_)) as u8;
                    if v_isSharedCheck_937_ == 0 {
                        v___x_928_ = v_a_922_;
                        v_isShared_929_ = v_isSharedCheck_937_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_926_);
                        lean_dec(v_a_922_);
                        v___x_928_ = lean_box(0);
                        v_isShared_929_ = v_isSharedCheck_937_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_924_);
                    lean_dec(v_a_922_);
                    v___x_938_ =
                        l_Lean_Meta_Grind_alreadyInternalized___redArg(v_eToInt_920_, v___y_910_);
                    if lean_obj_tag(v___x_938_) == 0 {
                        v_a_939_ = lean_ctor_get(v___x_938_, 0);
                        lean_inc(v_a_939_);
                        lean_dec_ref_known(v___x_938_, 1);
                        v___x_940_ = (lean_unbox(v_a_939_) as u8);
                        lean_dec(v_a_939_);
                        if v___x_940_ == 0 {
                            lean_dec_ref(v_eToInt_920_);
                            state = 2;
                            continue;
                        } else {
                            v___x_941_ = lean_st_ref_get(v___y_910_);
                            v___x_942_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(
                                v___x_941_,
                                v_eToInt_920_,
                                v___y_911_,
                                v___y_912_,
                                v___y_913_,
                                v___y_914_,
                            );
                            lean_dec(v___x_941_);
                            if lean_obj_tag(v___x_942_) == 0 {
                                v_a_943_ = lean_ctor_get(v___x_942_, 0);
                                lean_inc(v_a_943_);
                                lean_dec_ref_known(v___x_942_, 1);
                                if lean_obj_tag(v_a_943_) == 1 {
                                    v_val_944_ = lean_ctor_get(v_a_943_, 0);
                                    lean_inc(v_val_944_);
                                    lean_dec_ref_known(v_a_943_, 1);
                                    v_val_903_ = v_val_944_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_a_943_);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                return v___x_942_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_eToInt_920_);
                        v_a_945_ = lean_ctor_get(v___x_938_, 0);
                        v_isSharedCheck_952_ = (!lean_is_exclusive(v___x_938_)) as u8;
                        if v_isSharedCheck_952_ == 0 {
                            v___x_947_ = v___x_938_;
                            v_isShared_948_ = v_isSharedCheck_952_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_945_);
                            lean_dec(v___x_938_);
                            v___x_947_ = lean_box(0);
                            v_isShared_948_ = v_isSharedCheck_952_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_930_ = l_Rat_ofInt(v_val_926_);
                if v_isShared_929_ == 0 {
                    lean_ctor_set(v___x_928_, 0, v___x_930_);
                    v___x_932_ = v___x_928_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_930_);
                    v___x_932_ = v_reuseFailAlloc_936_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_925_ == 0 {
                    lean_ctor_set(v___x_924_, 0, v___x_932_);
                    v___x_934_ = v___x_924_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
                    v___x_934_ = v_reuseFailAlloc_935_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_934_;
            }
            8 => {
                if v_isShared_948_ == 0 {
                    v___x_950_ = v___x_947_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
                    v___x_950_ = v_reuseFailAlloc_951_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_950_;
            }
            10 => {
                if v_isShared_957_ == 0 {
                    v___x_959_ = v___x_956_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
                    v___x_959_ = v_reuseFailAlloc_960_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_959_;
            }
            12 => {
                if v_isShared_965_ == 0 {
                    v___x_967_ = v___x_964_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
                    v___x_967_ = v_reuseFailAlloc_968_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_967_;
            }
            14 => {
                v___x_979_ = l_Lean_Int_mkType;
                v___x_980_ = lean_expr_eqv(v_a_975_, v___x_979_);
                if v___x_980_ == 0 {
                    lean_del_object(v___x_977_);
                    v___x_981_ = l_Lean_Nat_mkType;
                    v___x_982_ = lean_expr_eqv(v_a_975_, v___x_981_);
                    lean_dec(v_a_975_);
                    if v___x_982_ == 0 {
                        v___x_983_ =
                            l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_891_, v_a_899_);
                        if lean_obj_tag(v___x_983_) == 0 {
                            v_a_984_ = lean_ctor_get(v___x_983_, 0);
                            lean_inc(v_a_984_);
                            lean_dec_ref_known(v___x_983_, 1);
                            v_toIntVarMap_985_ = lean_ctor_get(v_a_984_, 21);
                            lean_inc_ref(v_toIntVarMap_985_);
                            lean_dec(v_a_984_);
                            v___x_986_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_toIntVarMap_985_, v_e_890_);
                            lean_dec_ref(v_toIntVarMap_985_);
                            if lean_obj_tag(v___x_986_) == 1 {
                                v_val_987_ = lean_ctor_get(v___x_986_, 0);
                                lean_inc(v_val_987_);
                                lean_dec_ref_known(v___x_986_, 1);
                                v___x_988_ = lean_st_ref_get(v_a_891_);
                                v___x_989_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(
                                    v___x_988_, v_val_987_, v_a_897_, v_a_898_, v_a_899_, v_a_900_,
                                );
                                lean_dec(v___x_988_);
                                if lean_obj_tag(v___x_989_) == 0 {
                                    v_a_990_ = lean_ctor_get(v___x_989_, 0);
                                    lean_inc(v_a_990_);
                                    lean_dec_ref_known(v___x_989_, 1);
                                    if lean_obj_tag(v_a_990_) == 1 {
                                        lean_dec_ref(v_e_890_);
                                        v_val_991_ = lean_ctor_get(v_a_990_, 0);
                                        lean_inc(v_val_991_);
                                        lean_dec_ref_known(v_a_990_, 1);
                                        v_val_903_ = v_val_991_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v_a_990_);
                                        v___y_910_ = v_a_891_;
                                        v___y_911_ = v_a_897_;
                                        v___y_912_ = v_a_898_;
                                        v___y_913_ = v_a_899_;
                                        v___y_914_ = v_a_900_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_e_890_);
                                    return v___x_989_;
                                }
                            } else {
                                lean_dec(v___x_986_);
                                v___y_910_ = v_a_891_;
                                v___y_911_ = v_a_897_;
                                v___y_912_ = v_a_898_;
                                v___y_913_ = v_a_899_;
                                v___y_914_ = v_a_900_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_e_890_);
                            v_a_992_ = lean_ctor_get(v___x_983_, 0);
                            v_isSharedCheck_999_ = (!lean_is_exclusive(v___x_983_)) as u8;
                            if v_isSharedCheck_999_ == 0 {
                                v___x_994_ = v___x_983_;
                                v_isShared_995_ = v_isSharedCheck_999_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_992_);
                                lean_dec(v___x_983_);
                                v___x_994_ = lean_box(0);
                                v_isShared_995_ = v_isSharedCheck_999_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        v___x_1000_ = l_Lean_Meta_Grind_getParents___redArg(v_e_890_, v_a_891_);
                        lean_dec_ref(v_e_890_);
                        if lean_obj_tag(v___x_1000_) == 0 {
                            v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
                            lean_inc(v_a_1001_);
                            lean_dec_ref_known(v___x_1000_, 1);
                            v___x_1002_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1001_);
                            lean_dec(v_a_1001_);
                            v___x_1003_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__0;
                            v___x_1004_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg(v___x_1002_, v___x_1003_, v_a_891_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
                            lean_dec(v___x_1002_);
                            if lean_obj_tag(v___x_1004_) == 0 {
                                v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
                                v_isSharedCheck_1014_ = (!lean_is_exclusive(v___x_1004_)) as u8;
                                if v_isSharedCheck_1014_ == 0 {
                                    v___x_1007_ = v___x_1004_;
                                    v_isShared_1008_ = v_isSharedCheck_1014_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_1005_);
                                    lean_dec(v___x_1004_);
                                    v___x_1007_ = lean_box(0);
                                    v_isShared_1008_ = v_isSharedCheck_1014_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                v_a_1015_ = lean_ctor_get(v___x_1004_, 0);
                                v_isSharedCheck_1022_ = (!lean_is_exclusive(v___x_1004_)) as u8;
                                if v_isSharedCheck_1022_ == 0 {
                                    v___x_1017_ = v___x_1004_;
                                    v_isShared_1018_ = v_isSharedCheck_1022_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_1015_);
                                    lean_dec(v___x_1004_);
                                    v___x_1017_ = lean_box(0);
                                    v_isShared_1018_ = v_isSharedCheck_1022_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            v_a_1023_ = lean_ctor_get(v___x_1000_, 0);
                            v_isSharedCheck_1030_ = (!lean_is_exclusive(v___x_1000_)) as u8;
                            if v_isSharedCheck_1030_ == 0 {
                                v___x_1025_ = v___x_1000_;
                                v_isShared_1026_ = v_isSharedCheck_1030_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_1023_);
                                lean_dec(v___x_1000_);
                                v___x_1025_ = lean_box(0);
                                v_isShared_1026_ = v_isSharedCheck_1030_;
                                state = 21;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_975_);
                    lean_dec_ref(v_e_890_);
                    v___x_1031_ = lean_box(0);
                    if v_isShared_978_ == 0 {
                        lean_ctor_set(v___x_977_, 0, v___x_1031_);
                        v___x_1033_ = v___x_977_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
                        v___x_1033_ = v_reuseFailAlloc_1034_;
                        state = 23;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_995_ == 0 {
                    v___x_997_ = v___x_994_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
                    v___x_997_ = v_reuseFailAlloc_998_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_997_;
            }
            17 => {
                v_fst_1009_ = lean_ctor_get(v_a_1005_, 0);
                lean_inc(v_fst_1009_);
                lean_dec(v_a_1005_);
                if lean_obj_tag(v_fst_1009_) == 0 {
                    lean_del_object(v___x_1007_);
                    state = 2;
                    continue;
                } else {
                    v_val_1010_ = lean_ctor_get(v_fst_1009_, 0);
                    lean_inc(v_val_1010_);
                    lean_dec_ref_known(v_fst_1009_, 1);
                    if v_isShared_1008_ == 0 {
                        lean_ctor_set(v___x_1007_, 0, v_val_1010_);
                        v___x_1012_ = v___x_1007_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_val_1010_);
                        v___x_1012_ = v_reuseFailAlloc_1013_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                return v___x_1012_;
            }
            19 => {
                if v_isShared_1018_ == 0 {
                    v___x_1020_ = v___x_1017_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
                    v___x_1020_ = v_reuseFailAlloc_1021_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1020_;
            }
            21 => {
                if v_isShared_1026_ == 0 {
                    v___x_1028_ = v___x_1025_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
                    v___x_1028_ = v_reuseFailAlloc_1029_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1028_;
            }
            23 => {
                return v___x_1033_;
            }
            24 => {
                if v_isShared_1039_ == 0 {
                    v___x_1041_ = v___x_1038_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
                    v___x_1041_ = v_reuseFailAlloc_1042_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f___boxed(
    mut v_e_1044_: *mut LeanObject,
    mut v_a_1045_: *mut LeanObject,
    mut v_a_1046_: *mut LeanObject,
    mut v_a_1047_: *mut LeanObject,
    mut v_a_1048_: *mut LeanObject,
    mut v_a_1049_: *mut LeanObject,
    mut v_a_1050_: *mut LeanObject,
    mut v_a_1051_: *mut LeanObject,
    mut v_a_1052_: *mut LeanObject,
    mut v_a_1053_: *mut LeanObject,
    mut v_a_1054_: *mut LeanObject,
    mut v_a_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1056_: *mut LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_e_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
    lean_dec(v_a_1054_);
    lean_dec_ref(v_a_1053_);
    lean_dec(v_a_1052_);
    lean_dec_ref(v_a_1051_);
    lean_dec(v_a_1050_);
    lean_dec_ref(v_a_1049_);
    lean_dec(v_a_1048_);
    lean_dec_ref(v_a_1047_);
    lean_dec(v_a_1046_);
    lean_dec(v_a_1045_);
    return v_res_1056_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0(
    mut v_00_u03b2_1057_: *mut LeanObject,
    mut v_x_1058_: *mut LeanObject,
    mut v_x_1059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    v___x_1060_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_x_1058_, v_x_1059_);
    return v___x_1060_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___boxed(
    mut v_00_u03b2_1061_: *mut LeanObject,
    mut v_x_1062_: *mut LeanObject,
    mut v_x_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1064_: *mut LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0(v_00_u03b2_1061_, v_x_1062_, v_x_1063_);
    lean_dec_ref(v_x_1063_);
    lean_dec_ref(v_x_1062_);
    return v_res_1064_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2(
    mut v_as_1065_: *mut LeanObject,
    mut v_as_x27_1066_: *mut LeanObject,
    mut v_b_1067_: *mut LeanObject,
    mut v_a_1068_: *mut LeanObject,
    mut v___y_1069_: *mut LeanObject,
    mut v___y_1070_: *mut LeanObject,
    mut v___y_1071_: *mut LeanObject,
    mut v___y_1072_: *mut LeanObject,
    mut v___y_1073_: *mut LeanObject,
    mut v___y_1074_: *mut LeanObject,
    mut v___y_1075_: *mut LeanObject,
    mut v___y_1076_: *mut LeanObject,
    mut v___y_1077_: *mut LeanObject,
    mut v___y_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    v___x_1080_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg(v_as_x27_1066_, v_b_1067_, v___y_1069_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
    return v___x_1080_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___boxed(
    mut v_as_1081_: *mut LeanObject,
    mut v_as_x27_1082_: *mut LeanObject,
    mut v_b_1083_: *mut LeanObject,
    mut v_a_1084_: *mut LeanObject,
    mut v___y_1085_: *mut LeanObject,
    mut v___y_1086_: *mut LeanObject,
    mut v___y_1087_: *mut LeanObject,
    mut v___y_1088_: *mut LeanObject,
    mut v___y_1089_: *mut LeanObject,
    mut v___y_1090_: *mut LeanObject,
    mut v___y_1091_: *mut LeanObject,
    mut v___y_1092_: *mut LeanObject,
    mut v___y_1093_: *mut LeanObject,
    mut v___y_1094_: *mut LeanObject,
    mut v___y_1095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1096_: *mut LeanObject = core::ptr::null_mut();
    v_res_1096_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2(v_as_1081_, v_as_x27_1082_, v_b_1083_, v_a_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
    lean_dec(v___y_1094_);
    lean_dec_ref(v___y_1093_);
    lean_dec(v___y_1092_);
    lean_dec_ref(v___y_1091_);
    lean_dec(v___y_1090_);
    lean_dec_ref(v___y_1089_);
    lean_dec(v___y_1088_);
    lean_dec_ref(v___y_1087_);
    lean_dec(v___y_1086_);
    lean_dec(v___y_1085_);
    lean_dec(v_as_x27_1082_);
    lean_dec(v_as_1081_);
    return v_res_1096_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0(
    mut v_00_u03b2_1097_: *mut LeanObject,
    mut v_x_1098_: *mut LeanObject,
    mut v_x_1099_: usize,
    mut v_x_1100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg(v_x_1098_, v_x_1099_, v_x_1100_);
    return v___x_1101_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_1102_: *mut LeanObject,
    mut v_x_1103_: *mut LeanObject,
    mut v_x_1104_: *mut LeanObject,
    mut v_x_1105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_52562__boxed_1106_: usize = 0;
    let mut v_res_1107_: *mut LeanObject = core::ptr::null_mut();
    v_x_52562__boxed_1106_ = lean_unbox_usize(v_x_1104_);
    lean_dec(v_x_1104_);
    v_res_1107_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0(v_00_u03b2_1102_, v_x_1103_, v_x_52562__boxed_1106_, v_x_1105_);
    lean_dec_ref(v_x_1105_);
    lean_dec_ref(v_x_1103_);
    return v_res_1107_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1108_: *mut LeanObject,
    mut v_keys_1109_: *mut LeanObject,
    mut v_vals_1110_: *mut LeanObject,
    mut v_heq_1111_: *mut LeanObject,
    mut v_i_1112_: *mut LeanObject,
    mut v_k_1113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    v___x_1114_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg(v_keys_1109_, v_vals_1110_, v_i_1112_, v_k_1113_);
    return v___x_1114_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1115_: *mut LeanObject,
    mut v_keys_1116_: *mut LeanObject,
    mut v_vals_1117_: *mut LeanObject,
    mut v_heq_1118_: *mut LeanObject,
    mut v_i_1119_: *mut LeanObject,
    mut v_k_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1121_: *mut LeanObject = core::ptr::null_mut();
    v_res_1121_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2(v_00_u03b2_1115_, v_keys_1116_, v_vals_1117_, v_heq_1118_, v_i_1119_, v_k_1120_);
    lean_dec_ref(v_k_1120_);
    lean_dec_ref(v_vals_1117_);
    lean_dec_ref(v_keys_1116_);
    return v_res_1121_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(
    mut v_e_1122_: *mut LeanObject,
    mut v_a_1123_: *mut LeanObject,
    mut v_a_1124_: *mut LeanObject,
    mut v_a_1125_: *mut LeanObject,
    mut v_a_1126_: *mut LeanObject,
    mut v_a_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    v___x_1129_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
    v___x_1130_ = l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(
        v___x_1129_,
        v_e_1122_,
        v_a_1123_,
        v_a_1124_,
        v_a_1125_,
        v_a_1126_,
        v_a_1127_,
    );
    return v___x_1130_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg___boxed(
    mut v_e_1131_: *mut LeanObject,
    mut v_a_1132_: *mut LeanObject,
    mut v_a_1133_: *mut LeanObject,
    mut v_a_1134_: *mut LeanObject,
    mut v_a_1135_: *mut LeanObject,
    mut v_a_1136_: *mut LeanObject,
    mut v_a_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1138_: *mut LeanObject = core::ptr::null_mut();
    v_res_1138_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(v_e_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
    lean_dec(v_a_1136_);
    lean_dec_ref(v_a_1135_);
    lean_dec(v_a_1134_);
    lean_dec_ref(v_a_1133_);
    lean_dec(v_a_1132_);
    return v_res_1138_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar(
    mut v_e_1139_: *mut LeanObject,
    mut v_a_1140_: *mut LeanObject,
    mut v_a_1141_: *mut LeanObject,
    mut v_a_1142_: *mut LeanObject,
    mut v_a_1143_: *mut LeanObject,
    mut v_a_1144_: *mut LeanObject,
    mut v_a_1145_: *mut LeanObject,
    mut v_a_1146_: *mut LeanObject,
    mut v_a_1147_: *mut LeanObject,
    mut v_a_1148_: *mut LeanObject,
    mut v_a_1149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    v___x_1151_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(v_e_1139_, v_a_1140_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
    return v___x_1151_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___boxed(
    mut v_e_1152_: *mut LeanObject,
    mut v_a_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
    mut v_a_1155_: *mut LeanObject,
    mut v_a_1156_: *mut LeanObject,
    mut v_a_1157_: *mut LeanObject,
    mut v_a_1158_: *mut LeanObject,
    mut v_a_1159_: *mut LeanObject,
    mut v_a_1160_: *mut LeanObject,
    mut v_a_1161_: *mut LeanObject,
    mut v_a_1162_: *mut LeanObject,
    mut v_a_1163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1164_: *mut LeanObject = core::ptr::null_mut();
    v_res_1164_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar(v_e_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
    lean_dec(v_a_1162_);
    lean_dec_ref(v_a_1161_);
    lean_dec(v_a_1160_);
    lean_dec_ref(v_a_1159_);
    lean_dec(v_a_1158_);
    lean_dec_ref(v_a_1157_);
    lean_dec(v_a_1156_);
    lean_dec_ref(v_a_1155_);
    lean_dec(v_a_1154_);
    lean_dec(v_a_1153_);
    return v_res_1164_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(
    mut v_e_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
    mut v_a_1182_: *mut LeanObject,
    mut v_a_1183_: *mut LeanObject,
    mut v_a_1184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: u8 = 0;
    let mut v_arg_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: u8 = 0;
    let mut v_arg_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: u8 = 0;
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: u8 = 0;
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    let mut v_b_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: u8 = 0;
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1224_: u8 = 0;
    let mut v_a_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1228_: u8 = 0;
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1232_: u8 = 0;
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: u8 = 0;
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: u8 = 0;
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u8 = 0;
    let mut v___y_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1245_: u8 = 0;
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1254_: u8 = 0;
    let mut v_a_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1258_: u8 = 0;
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1262_: u8 = 0;
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1268_: u8 = 0;
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut v___x_1279_: u8 = 0;
    let mut v___x_1280_: u8 = 0;
    let mut v_a_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1284_: u8 = 0;
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1190_ = l_Lean_Expr_cleanupAnnotations(v_e_1180_);
                v___x_1191_ = l_Lean_Expr_isApp(v___x_1190_);
                if v___x_1191_ == 0 {
                    lean_dec_ref(v___x_1190_);
                    state = 1;
                    continue;
                } else {
                    v_arg_1192_ = lean_ctor_get(v___x_1190_, 1);
                    lean_inc_ref(v_arg_1192_);
                    v___x_1193_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1190_);
                    v___x_1194_ = l_Lean_Expr_isApp(v___x_1193_);
                    if v___x_1194_ == 0 {
                        lean_dec_ref(v___x_1193_);
                        lean_dec_ref(v_arg_1192_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_1195_ = lean_ctor_get(v___x_1193_, 1);
                        lean_inc_ref(v_arg_1195_);
                        v___x_1196_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1193_);
                        v___x_1197_ = l_Lean_Expr_isApp(v___x_1196_);
                        if v___x_1197_ == 0 {
                            lean_dec_ref(v___x_1196_);
                            lean_dec_ref(v_arg_1195_);
                            lean_dec_ref(v_arg_1192_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1198_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1196_);
                            v___x_1199_ = l_Lean_Expr_isApp(v___x_1198_);
                            if v___x_1199_ == 0 {
                                lean_dec_ref(v___x_1198_);
                                lean_dec_ref(v_arg_1195_);
                                lean_dec_ref(v_arg_1192_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1200_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1198_);
                                v___x_1201_ = l_Lean_Expr_isApp(v___x_1200_);
                                if v___x_1201_ == 0 {
                                    lean_dec_ref(v___x_1200_);
                                    lean_dec_ref(v_arg_1195_);
                                    lean_dec_ref(v_arg_1192_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1202_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1200_);
                                    v___x_1203_ = l_Lean_Expr_isApp(v___x_1202_);
                                    if v___x_1203_ == 0 {
                                        lean_dec_ref(v___x_1202_);
                                        lean_dec_ref(v_arg_1195_);
                                        lean_dec_ref(v_arg_1192_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1233_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_1202_);
                                        v___x_1234_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2;
                                        v___x_1235_ =
                                            l_Lean_Expr_isConstOf(v___x_1233_, v___x_1234_);
                                        if v___x_1235_ == 0 {
                                            v___x_1236_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5;
                                            v___x_1237_ =
                                                l_Lean_Expr_isConstOf(v___x_1233_, v___x_1236_);
                                            if v___x_1237_ == 0 {
                                                v___x_1238_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8;
                                                v___x_1239_ =
                                                    l_Lean_Expr_isConstOf(v___x_1233_, v___x_1238_);
                                                lean_dec_ref(v___x_1233_);
                                                if v___x_1239_ == 0 {
                                                    lean_dec_ref(v_arg_1195_);
                                                    lean_dec_ref(v_arg_1192_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_1263_ = l_Lean_Meta_saveState___redArg(
                                                        v_a_1182_, v_a_1184_,
                                                    );
                                                    if lean_obj_tag(v___x_1263_) == 0 {
                                                        v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
                                                        lean_inc(v_a_1264_);
                                                        lean_dec_ref_known(v___x_1263_, 1);
                                                        v___x_1265_ = l_Lean_Meta_getIntValue_x3f(
                                                            v_arg_1195_,
                                                            v_a_1181_,
                                                            v_a_1182_,
                                                            v_a_1183_,
                                                            v_a_1184_,
                                                        );
                                                        if lean_obj_tag(v___x_1265_) == 0 {
                                                            lean_dec(v_a_1264_);
                                                            lean_dec_ref(v_arg_1192_);
                                                            v___y_1241_ = v___x_1265_;
                                                            state = 8;
                                                            continue;
                                                        } else {
                                                            v_a_1266_ =
                                                                lean_ctor_get(v___x_1265_, 0);
                                                            lean_inc(v_a_1266_);
                                                            v___x_1279_ =
                                                                l_Lean_Exception_isInterrupt(
                                                                    v_a_1266_,
                                                                );
                                                            if v___x_1279_ == 0 {
                                                                v___x_1280_ =
                                                                    l_Lean_Exception_isRuntime(
                                                                        v_a_1266_,
                                                                    );
                                                                v___y_1268_ = v___x_1280_;
                                                                state = 14;
                                                                continue;
                                                            } else {
                                                                lean_dec(v_a_1266_);
                                                                v___y_1268_ = v___x_1279_;
                                                                state = 14;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_1195_);
                                                        lean_dec_ref(v_arg_1192_);
                                                        v_a_1281_ = lean_ctor_get(v___x_1263_, 0);
                                                        v_isSharedCheck_1288_ =
                                                            (!lean_is_exclusive(v___x_1263_)) as u8;
                                                        if v_isSharedCheck_1288_ == 0 {
                                                            v___x_1283_ = v___x_1263_;
                                                            v_isShared_1284_ =
                                                                v_isSharedCheck_1288_;
                                                            state = 17;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_1281_);
                                                            lean_dec(v___x_1263_);
                                                            v___x_1283_ = lean_box(0);
                                                            v_isShared_1284_ =
                                                                v_isSharedCheck_1288_;
                                                            state = 17;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_1233_);
                                                lean_dec_ref(v_arg_1195_);
                                                v_b_1205_ = v_arg_1192_;
                                                v___y_1206_ = v_a_1181_;
                                                v___y_1207_ = v_a_1182_;
                                                v___y_1208_ = v_a_1183_;
                                                v___y_1209_ = v_a_1184_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_1233_);
                                            lean_dec_ref(v_arg_1195_);
                                            v_b_1205_ = v_arg_1192_;
                                            v___y_1206_ = v_a_1181_;
                                            v___y_1207_ = v_a_1182_;
                                            v___y_1208_ = v_a_1183_;
                                            v___y_1209_ = v_a_1184_;
                                            state = 2;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1187_ = 0;
                v___x_1188_ = lean_box((v___x_1187_) as usize);
                v___x_1189_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1189_, 0, v___x_1188_);
                return v___x_1189_;
            }
            2 => {
                v___x_1210_ = l_Lean_Meta_getIntValue_x3f(
                    v_b_1205_,
                    v___y_1206_,
                    v___y_1207_,
                    v___y_1208_,
                    v___y_1209_,
                );
                if lean_obj_tag(v___x_1210_) == 0 {
                    v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
                    v_isSharedCheck_1224_ = (!lean_is_exclusive(v___x_1210_)) as u8;
                    if v_isSharedCheck_1224_ == 0 {
                        v___x_1213_ = v___x_1210_;
                        v_isShared_1214_ = v_isSharedCheck_1224_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1211_);
                        lean_dec(v___x_1210_);
                        v___x_1213_ = lean_box(0);
                        v_isShared_1214_ = v_isSharedCheck_1224_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1225_ = lean_ctor_get(v___x_1210_, 0);
                    v_isSharedCheck_1232_ = (!lean_is_exclusive(v___x_1210_)) as u8;
                    if v_isSharedCheck_1232_ == 0 {
                        v___x_1227_ = v___x_1210_;
                        v_isShared_1228_ = v_isSharedCheck_1232_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1225_);
                        lean_dec(v___x_1210_);
                        v___x_1227_ = lean_box(0);
                        v_isShared_1228_ = v_isSharedCheck_1232_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_1211_) == 0 {
                    v___x_1215_ = lean_box((v___x_1203_) as usize);
                    if v_isShared_1214_ == 0 {
                        lean_ctor_set(v___x_1213_, 0, v___x_1215_);
                        v___x_1217_ = v___x_1213_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
                        v___x_1217_ = v_reuseFailAlloc_1218_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_1211_, 1);
                    v___x_1219_ = 0;
                    v___x_1220_ = lean_box((v___x_1219_) as usize);
                    if v_isShared_1214_ == 0 {
                        lean_ctor_set(v___x_1213_, 0, v___x_1220_);
                        v___x_1222_ = v___x_1213_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
                        v___x_1222_ = v_reuseFailAlloc_1223_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1217_;
            }
            5 => {
                return v___x_1222_;
            }
            6 => {
                if v_isShared_1228_ == 0 {
                    v___x_1230_ = v___x_1227_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
                    v___x_1230_ = v_reuseFailAlloc_1231_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1230_;
            }
            8 => {
                if lean_obj_tag(v___y_1241_) == 0 {
                    v_a_1242_ = lean_ctor_get(v___y_1241_, 0);
                    v_isSharedCheck_1254_ = (!lean_is_exclusive(v___y_1241_)) as u8;
                    if v_isSharedCheck_1254_ == 0 {
                        v___x_1244_ = v___y_1241_;
                        v_isShared_1245_ = v_isSharedCheck_1254_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1242_);
                        lean_dec(v___y_1241_);
                        v___x_1244_ = lean_box(0);
                        v_isShared_1245_ = v_isSharedCheck_1254_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_a_1255_ = lean_ctor_get(v___y_1241_, 0);
                    v_isSharedCheck_1262_ = (!lean_is_exclusive(v___y_1241_)) as u8;
                    if v_isSharedCheck_1262_ == 0 {
                        v___x_1257_ = v___y_1241_;
                        v_isShared_1258_ = v_isSharedCheck_1262_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1255_);
                        lean_dec(v___y_1241_);
                        v___x_1257_ = lean_box(0);
                        v_isShared_1258_ = v_isSharedCheck_1262_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                if lean_obj_tag(v_a_1242_) == 0 {
                    v___x_1246_ = lean_box((v___x_1239_) as usize);
                    if v_isShared_1245_ == 0 {
                        lean_ctor_set(v___x_1244_, 0, v___x_1246_);
                        v___x_1248_ = v___x_1244_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
                        v___x_1248_ = v_reuseFailAlloc_1249_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_1242_, 1);
                    v___x_1250_ = lean_box((v___x_1237_) as usize);
                    if v_isShared_1245_ == 0 {
                        lean_ctor_set(v___x_1244_, 0, v___x_1250_);
                        v___x_1252_ = v___x_1244_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
                        v___x_1252_ = v_reuseFailAlloc_1253_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_1248_;
            }
            11 => {
                return v___x_1252_;
            }
            12 => {
                if v_isShared_1258_ == 0 {
                    v___x_1260_ = v___x_1257_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
                    v___x_1260_ = v_reuseFailAlloc_1261_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1260_;
            }
            14 => {
                if v___y_1268_ == 0 {
                    lean_dec_ref_known(v___x_1265_, 1);
                    v___x_1269_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_1264_, v_a_1182_, v_a_1184_);
                    lean_dec(v_a_1264_);
                    if lean_obj_tag(v___x_1269_) == 0 {
                        lean_dec_ref_known(v___x_1269_, 1);
                        v___x_1270_ = l_Lean_Meta_getIntValue_x3f(
                            v_arg_1192_,
                            v_a_1181_,
                            v_a_1182_,
                            v_a_1183_,
                            v_a_1184_,
                        );
                        v___y_1241_ = v___x_1270_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec_ref(v_arg_1192_);
                        v_a_1271_ = lean_ctor_get(v___x_1269_, 0);
                        v_isSharedCheck_1278_ = (!lean_is_exclusive(v___x_1269_)) as u8;
                        if v_isSharedCheck_1278_ == 0 {
                            v___x_1273_ = v___x_1269_;
                            v_isShared_1274_ = v_isSharedCheck_1278_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_1271_);
                            lean_dec(v___x_1269_);
                            v___x_1273_ = lean_box(0);
                            v_isShared_1274_ = v_isSharedCheck_1278_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1264_);
                    lean_dec_ref(v_arg_1192_);
                    v___y_1241_ = v___x_1265_;
                    state = 8;
                    continue;
                }
            }
            15 => {
                if v_isShared_1274_ == 0 {
                    v___x_1276_ = v___x_1273_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
                    v___x_1276_ = v_reuseFailAlloc_1277_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1276_;
            }
            17 => {
                if v_isShared_1284_ == 0 {
                    v___x_1286_ = v___x_1283_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
                    v___x_1286_ = v_reuseFailAlloc_1287_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___boxed(
    mut v_e_1289_: *mut LeanObject,
    mut v_a_1290_: *mut LeanObject,
    mut v_a_1291_: *mut LeanObject,
    mut v_a_1292_: *mut LeanObject,
    mut v_a_1293_: *mut LeanObject,
    mut v_a_1294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1295_: *mut LeanObject = core::ptr::null_mut();
    v_res_1295_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
    lean_dec(v_a_1293_);
    lean_dec_ref(v_a_1292_);
    lean_dec(v_a_1291_);
    lean_dec_ref(v_a_1290_);
    return v_res_1295_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(
    mut v_e_1296_: *mut LeanObject,
    mut v_a_1297_: *mut LeanObject,
    mut v_a_1298_: *mut LeanObject,
    mut v_a_1299_: *mut LeanObject,
    mut v_a_1300_: *mut LeanObject,
    mut v_a_1301_: *mut LeanObject,
    mut v_a_1302_: *mut LeanObject,
    mut v_a_1303_: *mut LeanObject,
    mut v_a_1304_: *mut LeanObject,
    mut v_a_1305_: *mut LeanObject,
    mut v_a_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    v___x_1308_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_1296_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
    return v___x_1308_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(
    mut v_e_1309_: *mut LeanObject,
    mut v_a_1310_: *mut LeanObject,
    mut v_a_1311_: *mut LeanObject,
    mut v_a_1312_: *mut LeanObject,
    mut v_a_1313_: *mut LeanObject,
    mut v_a_1314_: *mut LeanObject,
    mut v_a_1315_: *mut LeanObject,
    mut v_a_1316_: *mut LeanObject,
    mut v_a_1317_: *mut LeanObject,
    mut v_a_1318_: *mut LeanObject,
    mut v_a_1319_: *mut LeanObject,
    mut v_a_1320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1321_: *mut LeanObject = core::ptr::null_mut();
    v_res_1321_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
    lean_dec(v_a_1319_);
    lean_dec_ref(v_a_1318_);
    lean_dec(v_a_1317_);
    lean_dec_ref(v_a_1316_);
    lean_dec(v_a_1315_);
    lean_dec_ref(v_a_1314_);
    lean_dec(v_a_1313_);
    lean_dec_ref(v_a_1312_);
    lean_dec(v_a_1311_);
    lean_dec(v_a_1310_);
    return v_res_1321_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(
    mut v_e_1337_: *mut LeanObject,
    mut v_a_1338_: *mut LeanObject,
    mut v_a_1339_: *mut LeanObject,
    mut v_a_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: u8 = 0;
    let mut v_f_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1337_);
                v___x_1343_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_1337_);
                if v___x_1343_ == 0 {
                    v___x_1344_ = 1;
                    v_f_1345_ = l_Lean_Expr_getAppFn(v_e_1337_);
                    lean_dec_ref(v_e_1337_);
                    v___x_1346_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2;
                    v___x_1347_ = l_Lean_Expr_isConstOf(v_f_1345_, v___x_1346_);
                    if v___x_1347_ == 0 {
                        v___x_1348_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5;
                        v___x_1349_ = l_Lean_Expr_isConstOf(v_f_1345_, v___x_1348_);
                        if v___x_1349_ == 0 {
                            v___x_1350_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8;
                            v___x_1351_ = l_Lean_Expr_isConstOf(v_f_1345_, v___x_1350_);
                            lean_dec_ref(v_f_1345_);
                            v___x_1352_ = lean_box((v___x_1351_) as usize);
                            v___x_1353_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1353_, 0, v___x_1352_);
                            return v___x_1353_;
                        } else {
                            lean_dec_ref(v_f_1345_);
                            v___x_1354_ = lean_box((v___x_1344_) as usize);
                            v___x_1355_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1355_, 0, v___x_1354_);
                            return v___x_1355_;
                        }
                    } else {
                        lean_dec_ref(v_f_1345_);
                        v___x_1356_ = lean_box((v___x_1344_) as usize);
                        v___x_1357_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1357_, 0, v___x_1356_);
                        return v___x_1357_;
                    }
                } else {
                    v___x_1358_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
                    if lean_obj_tag(v___x_1358_) == 0 {
                        v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
                        v_isSharedCheck_1373_ = (!lean_is_exclusive(v___x_1358_)) as u8;
                        if v_isSharedCheck_1373_ == 0 {
                            v___x_1361_ = v___x_1358_;
                            v_isShared_1362_ = v_isSharedCheck_1373_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1359_);
                            lean_dec(v___x_1358_);
                            v___x_1361_ = lean_box(0);
                            v_isShared_1362_ = v_isSharedCheck_1373_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_1358_;
                    }
                }
            }
            1 => {
                v___x_1363_ = (lean_unbox(v_a_1359_) as u8);
                lean_dec(v_a_1359_);
                if v___x_1363_ == 0 {
                    v___x_1364_ = lean_box((v___x_1343_) as usize);
                    if v_isShared_1362_ == 0 {
                        lean_ctor_set(v___x_1361_, 0, v___x_1364_);
                        v___x_1366_ = v___x_1361_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
                        v___x_1366_ = v_reuseFailAlloc_1367_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1368_ = 0;
                    v___x_1369_ = lean_box((v___x_1368_) as usize);
                    if v_isShared_1362_ == 0 {
                        lean_ctor_set(v___x_1361_, 0, v___x_1369_);
                        v___x_1371_ = v___x_1361_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
                        v___x_1371_ = v_reuseFailAlloc_1372_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1366_;
            }
            3 => {
                return v___x_1371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___boxed(
    mut v_e_1374_: *mut LeanObject,
    mut v_a_1375_: *mut LeanObject,
    mut v_a_1376_: *mut LeanObject,
    mut v_a_1377_: *mut LeanObject,
    mut v_a_1378_: *mut LeanObject,
    mut v_a_1379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1380_: *mut LeanObject = core::ptr::null_mut();
    v_res_1380_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(v_e_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
    lean_dec(v_a_1378_);
    lean_dec_ref(v_a_1377_);
    lean_dec(v_a_1376_);
    lean_dec_ref(v_a_1375_);
    return v_res_1380_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted(
    mut v_e_1381_: *mut LeanObject,
    mut v_a_1382_: *mut LeanObject,
    mut v_a_1383_: *mut LeanObject,
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
    mut v_a_1388_: *mut LeanObject,
    mut v_a_1389_: *mut LeanObject,
    mut v_a_1390_: *mut LeanObject,
    mut v_a_1391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    v___x_1393_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(v_e_1381_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
    return v___x_1393_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___boxed(
    mut v_e_1394_: *mut LeanObject,
    mut v_a_1395_: *mut LeanObject,
    mut v_a_1396_: *mut LeanObject,
    mut v_a_1397_: *mut LeanObject,
    mut v_a_1398_: *mut LeanObject,
    mut v_a_1399_: *mut LeanObject,
    mut v_a_1400_: *mut LeanObject,
    mut v_a_1401_: *mut LeanObject,
    mut v_a_1402_: *mut LeanObject,
    mut v_a_1403_: *mut LeanObject,
    mut v_a_1404_: *mut LeanObject,
    mut v_a_1405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1406_: *mut LeanObject = core::ptr::null_mut();
    v_res_1406_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted(v_e_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
    lean_dec(v_a_1404_);
    lean_dec_ref(v_a_1403_);
    lean_dec(v_a_1402_);
    lean_dec_ref(v_a_1401_);
    lean_dec(v_a_1400_);
    lean_dec_ref(v_a_1399_);
    lean_dec(v_a_1398_);
    lean_dec_ref(v_a_1397_);
    lean_dec(v_a_1396_);
    lean_dec(v_a_1395_);
    return v_res_1406_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment(
    mut v_a_1407_: *mut LeanObject,
    mut v_b_1408_: *mut LeanObject,
    mut v_a_1409_: *mut LeanObject,
    mut v_a_1410_: *mut LeanObject,
    mut v_a_1411_: *mut LeanObject,
    mut v_a_1412_: *mut LeanObject,
    mut v_a_1413_: *mut LeanObject,
    mut v_a_1414_: *mut LeanObject,
    mut v_a_1415_: *mut LeanObject,
    mut v_a_1416_: *mut LeanObject,
    mut v_a_1417_: *mut LeanObject,
    mut v_a_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1424_: u8 = 0;
    let mut v_val_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v_val_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1442_: u8 = 0;
    let mut v_a_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1446_: u8 = 0;
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1450_: u8 = 0;
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut v_a_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1460_: u8 = 0;
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1420_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_a_1407_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
                if lean_obj_tag(v___x_1420_) == 0 {
                    v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
                    v_isSharedCheck_1456_ = (!lean_is_exclusive(v___x_1420_)) as u8;
                    if v_isSharedCheck_1456_ == 0 {
                        v___x_1423_ = v___x_1420_;
                        v_isShared_1424_ = v_isSharedCheck_1456_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1421_);
                        lean_dec(v___x_1420_);
                        v___x_1423_ = lean_box(0);
                        v_isShared_1424_ = v_isSharedCheck_1456_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_b_1408_);
                    v_a_1457_ = lean_ctor_get(v___x_1420_, 0);
                    v_isSharedCheck_1464_ = (!lean_is_exclusive(v___x_1420_)) as u8;
                    if v_isSharedCheck_1464_ == 0 {
                        v___x_1459_ = v___x_1420_;
                        v_isShared_1460_ = v_isSharedCheck_1464_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1457_);
                        lean_dec(v___x_1420_);
                        v___x_1459_ = lean_box(0);
                        v_isShared_1460_ = v_isSharedCheck_1464_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1421_) == 1 {
                    lean_del_object(v___x_1423_);
                    v_val_1425_ = lean_ctor_get(v_a_1421_, 0);
                    lean_inc(v_val_1425_);
                    lean_dec_ref_known(v_a_1421_, 1);
                    v___x_1426_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_b_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
                    if lean_obj_tag(v___x_1426_) == 0 {
                        v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
                        v_isSharedCheck_1442_ = (!lean_is_exclusive(v___x_1426_)) as u8;
                        if v_isSharedCheck_1442_ == 0 {
                            v___x_1429_ = v___x_1426_;
                            v_isShared_1430_ = v_isSharedCheck_1442_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1427_);
                            lean_dec(v___x_1426_);
                            v___x_1429_ = lean_box(0);
                            v_isShared_1430_ = v_isSharedCheck_1442_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_1425_);
                        v_a_1443_ = lean_ctor_get(v___x_1426_, 0);
                        v_isSharedCheck_1450_ = (!lean_is_exclusive(v___x_1426_)) as u8;
                        if v_isSharedCheck_1450_ == 0 {
                            v___x_1445_ = v___x_1426_;
                            v_isShared_1446_ = v_isSharedCheck_1450_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1443_);
                            lean_dec(v___x_1426_);
                            v___x_1445_ = lean_box(0);
                            v_isShared_1446_ = v_isSharedCheck_1450_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1421_);
                    lean_dec_ref(v_b_1408_);
                    v___x_1451_ = 0;
                    v___x_1452_ = lean_box((v___x_1451_) as usize);
                    if v_isShared_1424_ == 0 {
                        lean_ctor_set(v___x_1423_, 0, v___x_1452_);
                        v___x_1454_ = v___x_1423_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
                        v___x_1454_ = v_reuseFailAlloc_1455_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1427_) == 1 {
                    v_val_1431_ = lean_ctor_get(v_a_1427_, 0);
                    lean_inc(v_val_1431_);
                    lean_dec_ref_known(v_a_1427_, 1);
                    v___x_1432_ = l_instDecidableEqRat_decEq(v_val_1425_, v_val_1431_);
                    lean_dec(v_val_1431_);
                    lean_dec(v_val_1425_);
                    v___x_1433_ = lean_box((v___x_1432_) as usize);
                    if v_isShared_1430_ == 0 {
                        lean_ctor_set(v___x_1429_, 0, v___x_1433_);
                        v___x_1435_ = v___x_1429_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
                        v___x_1435_ = v_reuseFailAlloc_1436_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1427_);
                    lean_dec(v_val_1425_);
                    v___x_1437_ = 0;
                    v___x_1438_ = lean_box((v___x_1437_) as usize);
                    if v_isShared_1430_ == 0 {
                        lean_ctor_set(v___x_1429_, 0, v___x_1438_);
                        v___x_1440_ = v___x_1429_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
                        v___x_1440_ = v_reuseFailAlloc_1441_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1435_;
            }
            4 => {
                return v___x_1440_;
            }
            5 => {
                if v_isShared_1446_ == 0 {
                    v___x_1448_ = v___x_1445_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
                    v___x_1448_ = v_reuseFailAlloc_1449_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1448_;
            }
            7 => {
                return v___x_1454_;
            }
            8 => {
                if v_isShared_1460_ == 0 {
                    v___x_1462_ = v___x_1459_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
                    v___x_1462_ = v_reuseFailAlloc_1463_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment___boxed(
    mut v_a_1465_: *mut LeanObject,
    mut v_b_1466_: *mut LeanObject,
    mut v_a_1467_: *mut LeanObject,
    mut v_a_1468_: *mut LeanObject,
    mut v_a_1469_: *mut LeanObject,
    mut v_a_1470_: *mut LeanObject,
    mut v_a_1471_: *mut LeanObject,
    mut v_a_1472_: *mut LeanObject,
    mut v_a_1473_: *mut LeanObject,
    mut v_a_1474_: *mut LeanObject,
    mut v_a_1475_: *mut LeanObject,
    mut v_a_1476_: *mut LeanObject,
    mut v_a_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1478_: *mut LeanObject = core::ptr::null_mut();
    v_res_1478_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment(v_a_1465_, v_b_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
    lean_dec(v_a_1476_);
    lean_dec_ref(v_a_1475_);
    lean_dec(v_a_1474_);
    lean_dec_ref(v_a_1473_);
    lean_dec(v_a_1472_);
    lean_dec_ref(v_a_1471_);
    lean_dec(v_a_1470_);
    lean_dec_ref(v_a_1469_);
    lean_dec(v_a_1468_);
    lean_dec(v_a_1467_);
    return v_res_1478_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mbtc(
    mut v_a_1486_: *mut LeanObject,
    mut v_a_1487_: *mut LeanObject,
    mut v_a_1488_: *mut LeanObject,
    mut v_a_1489_: *mut LeanObject,
    mut v_a_1490_: *mut LeanObject,
    mut v_a_1491_: *mut LeanObject,
    mut v_a_1492_: *mut LeanObject,
    mut v_a_1493_: *mut LeanObject,
    mut v_a_1494_: *mut LeanObject,
    mut v_a_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    v___x_1497_ = l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3;
    v___x_1498_ = l_Lean_Meta_Grind_mbtc(
        v___x_1497_,
        v_a_1486_,
        v_a_1487_,
        v_a_1488_,
        v_a_1489_,
        v_a_1490_,
        v_a_1491_,
        v_a_1492_,
        v_a_1493_,
        v_a_1494_,
        v_a_1495_,
    );
    return v___x_1498_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mbtc___boxed(
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
    mut v_a_1501_: *mut LeanObject,
    mut v_a_1502_: *mut LeanObject,
    mut v_a_1503_: *mut LeanObject,
    mut v_a_1504_: *mut LeanObject,
    mut v_a_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
    mut v_a_1507_: *mut LeanObject,
    mut v_a_1508_: *mut LeanObject,
    mut v_a_1509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1510_: *mut LeanObject = core::ptr::null_mut();
    v_res_1510_ = l_Lean_Meta_Grind_Arith_Cutsat_mbtc(
        v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_,
        v_a_1507_, v_a_1508_,
    );
    lean_dec(v_a_1508_);
    lean_dec_ref(v_a_1507_);
    lean_dec(v_a_1506_);
    lean_dec_ref(v_a_1505_);
    lean_dec(v_a_1504_);
    lean_dec_ref(v_a_1503_);
    lean_dec(v_a_1502_);
    lean_dec_ref(v_a_1501_);
    lean_dec(v_a_1500_);
    lean_dec(v_a_1499_);
    return v_res_1510_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
}

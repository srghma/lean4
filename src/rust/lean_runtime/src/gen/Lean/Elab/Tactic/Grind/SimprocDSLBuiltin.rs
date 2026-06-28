// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.SimprocDSLBuiltin
// Imports: Lean.Elab.Tactic.Grind.SimprocDSL Init.Sym.Simp.SimprocDSL Lean.Meta.Sym.Simp.EvalGround Lean.Meta.Sym.Simp.Telescope Lean.Meta.Sym.Simp.ControlFlow Lean.Meta.Sym.Simp.Forall Lean.Meta.Sym.Simp.Rewrite
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr5, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_replaceRef,
};
use crate::r#gen::Init::Sym::Simp::SimprocDSL::{
    initialize_Init_Sym_Simp_SimprocDSL, runtime_initialize_Init_Sym_Simp_SimprocDSL,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Grind::SimprocDSL::{
    initialize_Lean_Elab_Tactic_Grind_SimprocDSL, l_Lean_Elab_Tactic_Grind_elabSymDischarger,
    l_Lean_Elab_Tactic_Grind_elabSymSimproc, l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute,
    l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute,
    runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::Simp::ControlFlow::{
    initialize_Lean_Meta_Sym_Simp_ControlFlow, l_Lean_Meta_Sym_Simp_simpControl___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Discharger::{
    l_Lean_Meta_Sym_Simp_dischargeNone___boxed, l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed,
};
use crate::r#gen::Lean::Meta::Sym::Simp::EvalGround::{
    initialize_Lean_Meta_Sym_Simp_EvalGround, l_Lean_Meta_Sym_Simp_evalGround___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_EvalGround,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Forall::{
    initialize_Lean_Meta_Sym_Simp_Forall, l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_Forall,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Result::l_Lean_Meta_Sym_Simp_mkEqTrans___redArg;
use crate::r#gen::Lean::Meta::Sym::Simp::Rewrite::{
    initialize_Lean_Meta_Sym_Simp_Rewrite, l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_Rewrite,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    l_Lean_Meta_Sym_Simp_Result_withContextDependent, l_Lean_Meta_Sym_Simp_simp___boxed,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Telescope::{
    initialize_Lean_Meta_Sym_Simp_Telescope, l_Lean_Meta_Sym_Simp_simpTelescope___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_Telescope,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Theorems::{
    l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg,
    l_Lean_Meta_Sym_Simp_Theorems_insert, l_Lean_Meta_Sym_Simp_getSymSimpExtension_x3f,
    l_Lean_Meta_Sym_Simp_mkTheoremFromDecl,
};
use crate::r#gen::Lean::ReservedNameAction::l_Lean_realizeGlobalConstNoOverload;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_11, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_evalGround___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 1, m_objs: [((( 255 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 114, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__4_value) as *mut LeanObject,15642365844547147657 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__6_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__9_value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__11_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__11_value) as *mut LeanObject,5409699204079762053 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__13_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__13_value) as *mut LeanObject,4907018543776028915 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__15_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 105, 109, 112, 114, 111, 99, 68, 83, 76, 66, 117, 105, 108, 116, 105, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__14_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__15_value) as *mut LeanObject,16249163007935939648 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__16_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,5385254338892450297 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__17_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,4693334292471861852 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__18_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__9_value) as *mut LeanObject,3389843619649221974 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__19_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__11_value) as *mut LeanObject,14478700687058776363 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__20_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__13_value) as *mut LeanObject,16293275684050261757 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__22_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 71, 114, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__22_value) as *mut LeanObject,14723896219049396130 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__23_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_simpTelescope___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 108, 101, 115, 99, 111, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__0_value) as *mut LeanObject,4998230570037354350 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 84, 101, 108, 101, 115, 99, 111, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__2_value) as *mut LeanObject,6770449457282690577 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_simpControl___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 110, 116, 114, 111, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__0_value) as *mut LeanObject,5081612414781455787 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__2_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 67, 111, 110, 116, 114, 111, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__2_value) as *mut LeanObject,6182495194412741250 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_simp___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__1_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 114, 114, 111, 119, 84, 101, 108, 101, 115, 99, 111, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__0_value) as *mut LeanObject,7377854587226246167 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__2_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 65, 114, 114, 111, 119, 84, 101, 108, 101, 115, 99, 111, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__2_value) as *mut LeanObject,11648593786210260458 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 101, 108, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__0_value) as *mut LeanObject,3624192759600632721 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__2_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 83, 101, 108, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__2_value) as *mut LeanObject,10598441156433296818 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__0_value) as *mut LeanObject,5819120222105569584 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__2_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 78, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__2_value) as *mut LeanObject,13045445119418784023 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_dischargeNone___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 119, 114, 105, 116, 101, 83, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__0_value) as *mut LeanObject,10120069549607349517 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__2_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 83, 121, 109, 46, 115, 105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 32, 115, 101, 116, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__6_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 82, 101, 119, 114, 105, 116, 101, 83, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__0_value) as *mut LeanObject,16264364062687217872 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 119, 114, 105, 116, 101, 73, 110, 108, 105, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__2_value) as *mut LeanObject,5467082909805454615 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__4_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 82, 101, 119, 114, 105, 116, 101, 73, 110, 108, 105, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__0_value) as *mut LeanObject,17295928722472936712 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 84, 104, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__0_value) as *mut LeanObject,564218847374344423 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 65, 110, 100, 84, 104, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__0_value) as *mut LeanObject,10140887910739941129 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 114, 69, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__0_value) as *mut LeanObject,11113107058493755383 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 79, 114, 69, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__0_value) as *mut LeanObject,11181433736188212634 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 105, 109, 112, 114, 111, 99, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__0_value) as *mut LeanObject,15836888127685990580 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__0_value) as *mut LeanObject,13499288908001983991 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 115, 99, 104, 83, 101, 108, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__0_value) as *mut LeanObject,16169981844629337600 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 108, 97, 98, 68, 105, 115, 99, 104, 83, 101, 108, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__2_value) as *mut LeanObject,5948902922022391747 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 115, 99, 104, 78, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__0_value) as *mut LeanObject,12137791703934599550 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 108, 97, 98, 68, 105, 115, 99, 104, 78, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__2_value) as *mut LeanObject,6880829856682481277 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 105, 115, 99, 104, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut LeanObject,17473872748478919658 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut LeanObject,17762876748869580590 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__0_value) as *mut LeanObject,381305762770861206 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 68, 105, 115, 99, 104, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__0_value) as *mut LeanObject,14580698448265653145 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg()
-> *mut LeanObject {
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    v___x_1394_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg___closed__0;
    v___x_1395_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1395_, 0, v___x_1394_);
    return v___x_1395_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg___boxed(
    mut v_a_1396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1397_: *mut LeanObject = core::ptr::null_mut();
    v_res_1397_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg();
    return v_res_1397_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround(
    mut v_x_1398_: *mut LeanObject,
    mut v_a_1399_: *mut LeanObject,
    mut v_a_1400_: *mut LeanObject,
    mut v_a_1401_: *mut LeanObject,
    mut v_a_1402_: *mut LeanObject,
    mut v_a_1403_: *mut LeanObject,
    mut v_a_1404_: *mut LeanObject,
    mut v_a_1405_: *mut LeanObject,
    mut v_a_1406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    v___x_1408_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg();
    return v___x_1408_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___boxed(
    mut v_x_1409_: *mut LeanObject,
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
    let mut v_res_1419_: *mut LeanObject = core::ptr::null_mut();
    v_res_1419_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround(v_x_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_);
    lean_dec(v_a_1417_);
    lean_dec_ref(v_a_1416_);
    lean_dec(v_a_1415_);
    lean_dec_ref(v_a_1414_);
    lean_dec(v_a_1413_);
    lean_dec_ref(v_a_1412_);
    lean_dec(v_a_1411_);
    lean_dec_ref(v_a_1410_);
    lean_dec(v_x_1409_);
    return v_res_1419_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1()
-> *mut LeanObject {
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    v___x_1474_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1475_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5;
    v___x_1476_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__23;
    v___x_1477_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1478_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1474_,
        v___x_1475_,
        v___x_1476_,
        v___x_1477_,
    );
    return v___x_1478_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___boxed(
    mut v_a_1479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1480_: *mut LeanObject = core::ptr::null_mut();
    v_res_1480_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1();
    return v_res_1480_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg()
-> *mut LeanObject {
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    v___x_1483_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg___closed__0;
    v___x_1484_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1484_, 0, v___x_1483_);
    return v___x_1484_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg___boxed(
    mut v_a_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1486_: *mut LeanObject = core::ptr::null_mut();
    v_res_1486_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg();
    return v_res_1486_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope(
    mut v_x_1487_: *mut LeanObject,
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
    v___x_1497_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg();
    return v___x_1497_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___boxed(
    mut v_x_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
    mut v_a_1501_: *mut LeanObject,
    mut v_a_1502_: *mut LeanObject,
    mut v_a_1503_: *mut LeanObject,
    mut v_a_1504_: *mut LeanObject,
    mut v_a_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
    mut v_a_1507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1508_: *mut LeanObject = core::ptr::null_mut();
    v_res_1508_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope(v_x_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
    lean_dec(v_a_1506_);
    lean_dec_ref(v_a_1505_);
    lean_dec(v_a_1504_);
    lean_dec_ref(v_a_1503_);
    lean_dec(v_a_1502_);
    lean_dec_ref(v_a_1501_);
    lean_dec(v_a_1500_);
    lean_dec_ref(v_a_1499_);
    lean_dec(v_x_1498_);
    return v_res_1508_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1()
-> *mut LeanObject {
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    v___x_1521_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1522_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1;
    v___x_1523_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__3;
    v___x_1524_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1525_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1521_,
        v___x_1522_,
        v___x_1523_,
        v___x_1524_,
    );
    return v___x_1525_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___boxed(
    mut v_a_1526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1527_: *mut LeanObject = core::ptr::null_mut();
    v_res_1527_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1();
    return v_res_1527_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg()
-> *mut LeanObject {
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    v___x_1530_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg___closed__0;
    v___x_1531_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1531_, 0, v___x_1530_);
    return v___x_1531_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg___boxed(
    mut v_a_1532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1533_: *mut LeanObject = core::ptr::null_mut();
    v_res_1533_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg();
    return v_res_1533_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl(
    mut v_x_1534_: *mut LeanObject,
    mut v_a_1535_: *mut LeanObject,
    mut v_a_1536_: *mut LeanObject,
    mut v_a_1537_: *mut LeanObject,
    mut v_a_1538_: *mut LeanObject,
    mut v_a_1539_: *mut LeanObject,
    mut v_a_1540_: *mut LeanObject,
    mut v_a_1541_: *mut LeanObject,
    mut v_a_1542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    v___x_1544_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg();
    return v___x_1544_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___boxed(
    mut v_x_1545_: *mut LeanObject,
    mut v_a_1546_: *mut LeanObject,
    mut v_a_1547_: *mut LeanObject,
    mut v_a_1548_: *mut LeanObject,
    mut v_a_1549_: *mut LeanObject,
    mut v_a_1550_: *mut LeanObject,
    mut v_a_1551_: *mut LeanObject,
    mut v_a_1552_: *mut LeanObject,
    mut v_a_1553_: *mut LeanObject,
    mut v_a_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1555_: *mut LeanObject = core::ptr::null_mut();
    v_res_1555_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl(v_x_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
    lean_dec(v_a_1553_);
    lean_dec_ref(v_a_1552_);
    lean_dec(v_a_1551_);
    lean_dec_ref(v_a_1550_);
    lean_dec(v_a_1549_);
    lean_dec_ref(v_a_1548_);
    lean_dec(v_a_1547_);
    lean_dec_ref(v_a_1546_);
    lean_dec(v_x_1545_);
    return v_res_1555_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1()
-> *mut LeanObject {
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    v___x_1568_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1569_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1;
    v___x_1570_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__3;
    v___x_1571_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1572_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1568_,
        v___x_1569_,
        v___x_1570_,
        v___x_1571_,
    );
    return v___x_1572_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___boxed(
    mut v_a_1573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1574_: *mut LeanObject = core::ptr::null_mut();
    v_res_1574_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1();
    return v_res_1574_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg()
-> *mut LeanObject {
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    v___x_1579_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__1;
    v___x_1580_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1580_, 0, v___x_1579_);
    return v___x_1580_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___boxed(
    mut v_a_1581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1582_: *mut LeanObject = core::ptr::null_mut();
    v_res_1582_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg();
    return v_res_1582_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope(
    mut v_x_1583_: *mut LeanObject,
    mut v_a_1584_: *mut LeanObject,
    mut v_a_1585_: *mut LeanObject,
    mut v_a_1586_: *mut LeanObject,
    mut v_a_1587_: *mut LeanObject,
    mut v_a_1588_: *mut LeanObject,
    mut v_a_1589_: *mut LeanObject,
    mut v_a_1590_: *mut LeanObject,
    mut v_a_1591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    v___x_1593_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg();
    return v___x_1593_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___boxed(
    mut v_x_1594_: *mut LeanObject,
    mut v_a_1595_: *mut LeanObject,
    mut v_a_1596_: *mut LeanObject,
    mut v_a_1597_: *mut LeanObject,
    mut v_a_1598_: *mut LeanObject,
    mut v_a_1599_: *mut LeanObject,
    mut v_a_1600_: *mut LeanObject,
    mut v_a_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
    mut v_a_1603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1604_: *mut LeanObject = core::ptr::null_mut();
    v_res_1604_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope(v_x_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
    lean_dec(v_a_1602_);
    lean_dec_ref(v_a_1601_);
    lean_dec(v_a_1600_);
    lean_dec_ref(v_a_1599_);
    lean_dec(v_a_1598_);
    lean_dec_ref(v_a_1597_);
    lean_dec(v_a_1596_);
    lean_dec_ref(v_a_1595_);
    lean_dec(v_x_1594_);
    return v_res_1604_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1()
-> *mut LeanObject {
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    v___x_1617_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1618_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1;
    v___x_1619_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__3;
    v___x_1620_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1621_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1617_,
        v___x_1618_,
        v___x_1619_,
        v___x_1620_,
    );
    return v___x_1621_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___boxed(
    mut v_a_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1623_: *mut LeanObject = core::ptr::null_mut();
    v_res_1623_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1();
    return v_res_1623_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___redArg()
-> *mut LeanObject {
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    v___x_1625_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__0;
    v___x_1626_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1626_, 0, v___x_1625_);
    return v___x_1626_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___redArg___boxed(
    mut v_a_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1628_: *mut LeanObject = core::ptr::null_mut();
    v_res_1628_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___redArg();
    return v_res_1628_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf(
    mut v_x_1629_: *mut LeanObject,
    mut v_a_1630_: *mut LeanObject,
    mut v_a_1631_: *mut LeanObject,
    mut v_a_1632_: *mut LeanObject,
    mut v_a_1633_: *mut LeanObject,
    mut v_a_1634_: *mut LeanObject,
    mut v_a_1635_: *mut LeanObject,
    mut v_a_1636_: *mut LeanObject,
    mut v_a_1637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    v___x_1639_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___redArg();
    return v___x_1639_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___boxed(
    mut v_x_1640_: *mut LeanObject,
    mut v_a_1641_: *mut LeanObject,
    mut v_a_1642_: *mut LeanObject,
    mut v_a_1643_: *mut LeanObject,
    mut v_a_1644_: *mut LeanObject,
    mut v_a_1645_: *mut LeanObject,
    mut v_a_1646_: *mut LeanObject,
    mut v_a_1647_: *mut LeanObject,
    mut v_a_1648_: *mut LeanObject,
    mut v_a_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1650_: *mut LeanObject = core::ptr::null_mut();
    v_res_1650_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf(v_x_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
    lean_dec(v_a_1648_);
    lean_dec_ref(v_a_1647_);
    lean_dec(v_a_1646_);
    lean_dec_ref(v_a_1645_);
    lean_dec(v_a_1644_);
    lean_dec_ref(v_a_1643_);
    lean_dec(v_a_1642_);
    lean_dec_ref(v_a_1641_);
    lean_dec(v_x_1640_);
    return v_res_1650_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1()
-> *mut LeanObject {
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1664_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1;
    v___x_1665_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__3;
    v___x_1666_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1667_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1663_,
        v___x_1664_,
        v___x_1665_,
        v___x_1666_,
    );
    return v___x_1667_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___boxed(
    mut v_a_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1669_: *mut LeanObject = core::ptr::null_mut();
    v_res_1669_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1();
    return v_res_1669_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0(
    mut v_x_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    v___x_1683_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___closed__0;
    v___x_1684_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1684_, 0, v___x_1683_);
    return v___x_1684_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___boxed(
    mut v_x_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
    mut v___y_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1696_: *mut LeanObject = core::ptr::null_mut();
    v_res_1696_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0(v_x_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
    lean_dec(v___y_1694_);
    lean_dec_ref(v___y_1693_);
    lean_dec(v___y_1692_);
    lean_dec_ref(v___y_1691_);
    lean_dec(v___y_1690_);
    lean_dec_ref(v___y_1689_);
    lean_dec(v___y_1688_);
    lean_dec_ref(v___y_1687_);
    lean_dec(v___y_1686_);
    lean_dec_ref(v_x_1685_);
    return v_res_1696_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg()
-> *mut LeanObject {
    let mut v___f_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    v___f_1699_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___closed__0;
    v___x_1700_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1700_, 0, v___f_1699_);
    return v___x_1700_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___boxed(
    mut v_a_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1702_: *mut LeanObject = core::ptr::null_mut();
    v_res_1702_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg();
    return v_res_1702_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone(
    mut v_x_1703_: *mut LeanObject,
    mut v_a_1704_: *mut LeanObject,
    mut v_a_1705_: *mut LeanObject,
    mut v_a_1706_: *mut LeanObject,
    mut v_a_1707_: *mut LeanObject,
    mut v_a_1708_: *mut LeanObject,
    mut v_a_1709_: *mut LeanObject,
    mut v_a_1710_: *mut LeanObject,
    mut v_a_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    v___x_1713_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg();
    return v___x_1713_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___boxed(
    mut v_x_1714_: *mut LeanObject,
    mut v_a_1715_: *mut LeanObject,
    mut v_a_1716_: *mut LeanObject,
    mut v_a_1717_: *mut LeanObject,
    mut v_a_1718_: *mut LeanObject,
    mut v_a_1719_: *mut LeanObject,
    mut v_a_1720_: *mut LeanObject,
    mut v_a_1721_: *mut LeanObject,
    mut v_a_1722_: *mut LeanObject,
    mut v_a_1723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1724_: *mut LeanObject = core::ptr::null_mut();
    v_res_1724_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone(v_x_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_);
    lean_dec(v_a_1722_);
    lean_dec_ref(v_a_1721_);
    lean_dec(v_a_1720_);
    lean_dec_ref(v_a_1719_);
    lean_dec(v_a_1718_);
    lean_dec_ref(v_a_1717_);
    lean_dec(v_a_1716_);
    lean_dec_ref(v_a_1715_);
    lean_dec(v_x_1714_);
    return v_res_1724_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1()
-> *mut LeanObject {
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    v___x_1737_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1738_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1;
    v___x_1739_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__3;
    v___x_1740_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1741_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1737_,
        v___x_1738_,
        v___x_1739_,
        v___x_1740_,
    );
    return v___x_1741_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___boxed(
    mut v_a_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1743_: *mut LeanObject = core::ptr::null_mut();
    v_res_1743_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1();
    return v_res_1743_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger(
    mut v_discharger_x3f_1745_: *mut LeanObject,
    mut v_a_1746_: *mut LeanObject,
    mut v_a_1747_: *mut LeanObject,
    mut v_a_1748_: *mut LeanObject,
    mut v_a_1749_: *mut LeanObject,
    mut v_a_1750_: *mut LeanObject,
    mut v_a_1751_: *mut LeanObject,
    mut v_a_1752_: *mut LeanObject,
    mut v_a_1753_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_discharger_x3f_1745_) == 1 {
        let mut v_val_1755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
        v_val_1755_ = lean_ctor_get(v_discharger_x3f_1745_, 0);
        lean_inc(v_val_1755_);
        lean_dec_ref_known(v_discharger_x3f_1745_, 1);
        v___x_1756_ = l_Lean_Elab_Tactic_Grind_elabSymDischarger(
            v_val_1755_,
            v_a_1746_,
            v_a_1747_,
            v_a_1748_,
            v_a_1749_,
            v_a_1750_,
            v_a_1751_,
            v_a_1752_,
            v_a_1753_,
        );
        return v___x_1756_;
    } else {
        let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_discharger_x3f_1745_);
        v___x_1757_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0;
        v___x_1758_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1758_, 0, v___x_1757_);
        return v___x_1758_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___boxed(
    mut v_discharger_x3f_1759_: *mut LeanObject,
    mut v_a_1760_: *mut LeanObject,
    mut v_a_1761_: *mut LeanObject,
    mut v_a_1762_: *mut LeanObject,
    mut v_a_1763_: *mut LeanObject,
    mut v_a_1764_: *mut LeanObject,
    mut v_a_1765_: *mut LeanObject,
    mut v_a_1766_: *mut LeanObject,
    mut v_a_1767_: *mut LeanObject,
    mut v_a_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1769_: *mut LeanObject = core::ptr::null_mut();
    v_res_1769_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger(v_discharger_x3f_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
    lean_dec(v_a_1767_);
    lean_dec_ref(v_a_1766_);
    lean_dec(v_a_1765_);
    lean_dec_ref(v_a_1764_);
    lean_dec(v_a_1763_);
    lean_dec_ref(v_a_1762_);
    lean_dec(v_a_1761_);
    lean_dec_ref(v_a_1760_);
    return v_res_1769_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    v___x_1770_ = lean_box(0);
    v___x_1771_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1772_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1772_, 0, v___x_1771_);
    lean_ctor_set(v___x_1772_, 1, v___x_1770_);
    return v___x_1772_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    v___x_1774_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0);
    v___x_1775_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1775_, 0, v___x_1774_);
    return v___x_1775_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___boxed(
    mut v___y_1776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1777_: *mut LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
    return v_res_1777_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0(
    mut v_00_u03b1_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    v___x_1788_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
    return v___x_1788_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___boxed(
    mut v_00_u03b1_1789_: *mut LeanObject,
    mut v___y_1790_: *mut LeanObject,
    mut v___y_1791_: *mut LeanObject,
    mut v___y_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
    mut v___y_1794_: *mut LeanObject,
    mut v___y_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
    mut v___y_1797_: *mut LeanObject,
    mut v___y_1798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1799_: *mut LeanObject = core::ptr::null_mut();
    v_res_1799_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0(v_00_u03b1_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
    lean_dec(v___y_1797_);
    lean_dec_ref(v___y_1796_);
    lean_dec(v___y_1795_);
    lean_dec_ref(v___y_1794_);
    lean_dec(v___y_1793_);
    lean_dec_ref(v___y_1792_);
    lean_dec(v___y_1791_);
    lean_dec_ref(v___y_1790_);
    return v_res_1799_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1_spec__2(
    mut v_msgData_1800_: *mut LeanObject,
    mut v___y_1801_: *mut LeanObject,
    mut v___y_1802_: *mut LeanObject,
    mut v___y_1803_: *mut LeanObject,
    mut v___y_1804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    v___x_1806_ = lean_st_ref_get(v___y_1804_);
    v_env_1807_ = lean_ctor_get(v___x_1806_, 0);
    lean_inc_ref(v_env_1807_);
    lean_dec(v___x_1806_);
    v___x_1808_ = lean_st_ref_get(v___y_1802_);
    v_mctx_1809_ = lean_ctor_get(v___x_1808_, 0);
    lean_inc_ref(v_mctx_1809_);
    lean_dec(v___x_1808_);
    v_lctx_1810_ = lean_ctor_get(v___y_1801_, 2);
    v_options_1811_ = lean_ctor_get(v___y_1803_, 2);
    lean_inc_ref(v_options_1811_);
    lean_inc_ref(v_lctx_1810_);
    v___x_1812_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1812_, 0, v_env_1807_);
    lean_ctor_set(v___x_1812_, 1, v_mctx_1809_);
    lean_ctor_set(v___x_1812_, 2, v_lctx_1810_);
    lean_ctor_set(v___x_1812_, 3, v_options_1811_);
    v___x_1813_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    lean_ctor_set(v___x_1813_, 1, v_msgData_1800_);
    v___x_1814_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1814_, 0, v___x_1813_);
    return v___x_1814_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1821_: *mut LeanObject = core::ptr::null_mut();
    v_res_1821_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1_spec__2(v_msgData_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
    lean_dec(v___y_1819_);
    lean_dec_ref(v___y_1818_);
    lean_dec(v___y_1817_);
    lean_dec_ref(v___y_1816_);
    return v_res_1821_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___redArg(
    mut v_msg_1822_: *mut LeanObject,
    mut v___y_1823_: *mut LeanObject,
    mut v___y_1824_: *mut LeanObject,
    mut v___y_1825_: *mut LeanObject,
    mut v___y_1826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1828_ = lean_ctor_get(v___y_1825_, 5);
                v___x_1829_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1_spec__2(v_msg_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
                v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
                v_isSharedCheck_1838_ = (!lean_is_exclusive(v___x_1829_)) as u8;
                if v_isSharedCheck_1838_ == 0 {
                    v___x_1832_ = v___x_1829_;
                    v_isShared_1833_ = v_isSharedCheck_1838_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1830_);
                    lean_dec(v___x_1829_);
                    v___x_1832_ = lean_box(0);
                    v_isShared_1833_ = v_isSharedCheck_1838_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1828_);
                v___x_1834_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1834_, 0, v_ref_1828_);
                lean_ctor_set(v___x_1834_, 1, v_a_1830_);
                if v_isShared_1833_ == 0 {
                    lean_ctor_set_tag(v___x_1832_, 1);
                    lean_ctor_set(v___x_1832_, 0, v___x_1834_);
                    v___x_1836_ = v___x_1832_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
                    v___x_1836_ = v_reuseFailAlloc_1837_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___redArg___boxed(
    mut v_msg_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1845_: *mut LeanObject = core::ptr::null_mut();
    v_res_1845_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___redArg(v_msg_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
    lean_dec(v___y_1843_);
    lean_dec_ref(v___y_1842_);
    lean_dec(v___y_1841_);
    lean_dec_ref(v___y_1840_);
    return v_res_1845_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___redArg(
    mut v_ref_1846_: *mut LeanObject,
    mut v_msg_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1869_: u8 = 0;
    let mut v_cancelTk_x3f_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1871_: u8 = 0;
    let mut v_inheritedTraceOptions_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1857_ = lean_ctor_get(v___y_1854_, 0);
    v_fileMap_1858_ = lean_ctor_get(v___y_1854_, 1);
    v_options_1859_ = lean_ctor_get(v___y_1854_, 2);
    v_currRecDepth_1860_ = lean_ctor_get(v___y_1854_, 3);
    v_maxRecDepth_1861_ = lean_ctor_get(v___y_1854_, 4);
    v_ref_1862_ = lean_ctor_get(v___y_1854_, 5);
    v_currNamespace_1863_ = lean_ctor_get(v___y_1854_, 6);
    v_openDecls_1864_ = lean_ctor_get(v___y_1854_, 7);
    v_initHeartbeats_1865_ = lean_ctor_get(v___y_1854_, 8);
    v_maxHeartbeats_1866_ = lean_ctor_get(v___y_1854_, 9);
    v_quotContext_1867_ = lean_ctor_get(v___y_1854_, 10);
    v_currMacroScope_1868_ = lean_ctor_get(v___y_1854_, 11);
    v_diag_1869_ = lean_ctor_get_uint8(
        v___y_1854_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1870_ = lean_ctor_get(v___y_1854_, 12);
    v_suppressElabErrors_1871_ = lean_ctor_get_uint8(
        v___y_1854_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1872_ = lean_ctor_get(v___y_1854_, 13);
    v_ref_1873_ = l_Lean_replaceRef(v_ref_1846_, v_ref_1862_);
    lean_inc_ref(v_inheritedTraceOptions_1872_);
    lean_inc(v_cancelTk_x3f_1870_);
    lean_inc(v_currMacroScope_1868_);
    lean_inc(v_quotContext_1867_);
    lean_inc(v_maxHeartbeats_1866_);
    lean_inc(v_initHeartbeats_1865_);
    lean_inc(v_openDecls_1864_);
    lean_inc(v_currNamespace_1863_);
    lean_inc(v_maxRecDepth_1861_);
    lean_inc(v_currRecDepth_1860_);
    lean_inc_ref(v_options_1859_);
    lean_inc_ref(v_fileMap_1858_);
    lean_inc_ref(v_fileName_1857_);
    v___x_1874_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1874_, 0, v_fileName_1857_);
    lean_ctor_set(v___x_1874_, 1, v_fileMap_1858_);
    lean_ctor_set(v___x_1874_, 2, v_options_1859_);
    lean_ctor_set(v___x_1874_, 3, v_currRecDepth_1860_);
    lean_ctor_set(v___x_1874_, 4, v_maxRecDepth_1861_);
    lean_ctor_set(v___x_1874_, 5, v_ref_1873_);
    lean_ctor_set(v___x_1874_, 6, v_currNamespace_1863_);
    lean_ctor_set(v___x_1874_, 7, v_openDecls_1864_);
    lean_ctor_set(v___x_1874_, 8, v_initHeartbeats_1865_);
    lean_ctor_set(v___x_1874_, 9, v_maxHeartbeats_1866_);
    lean_ctor_set(v___x_1874_, 10, v_quotContext_1867_);
    lean_ctor_set(v___x_1874_, 11, v_currMacroScope_1868_);
    lean_ctor_set(v___x_1874_, 12, v_cancelTk_x3f_1870_);
    lean_ctor_set(v___x_1874_, 13, v_inheritedTraceOptions_1872_);
    lean_ctor_set_uint8(
        v___x_1874_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1869_,
    );
    lean_ctor_set_uint8(
        v___x_1874_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1871_,
    );
    v___x_1875_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___redArg(v_msg_1847_, v___y_1852_, v___y_1853_, v___x_1874_, v___y_1855_);
    lean_dec_ref_known(v___x_1874_, 14);
    return v___x_1875_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___redArg___boxed(
    mut v_ref_1876_: *mut LeanObject,
    mut v_msg_1877_: *mut LeanObject,
    mut v___y_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
    mut v___y_1883_: *mut LeanObject,
    mut v___y_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1887_: *mut LeanObject = core::ptr::null_mut();
    v_res_1887_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___redArg(v_ref_1876_, v_msg_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
    lean_dec(v___y_1885_);
    lean_dec_ref(v___y_1884_);
    lean_dec(v___y_1883_);
    lean_dec_ref(v___y_1882_);
    lean_dec(v___y_1881_);
    lean_dec_ref(v___y_1880_);
    lean_dec(v___y_1879_);
    lean_dec_ref(v___y_1878_);
    lean_dec(v_ref_1876_);
    return v_res_1887_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3()
-> *mut LeanObject {
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    v___x_1896_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__2;
    v___x_1897_ = l_Lean_stringToMessageData(v___x_1896_);
    return v___x_1897_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5()
-> *mut LeanObject {
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    v___x_1899_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__4;
    v___x_1900_ = l_Lean_stringToMessageData(v___x_1899_);
    return v___x_1900_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet(
    mut v_stx_1904_: *mut LeanObject,
    mut v_a_1905_: *mut LeanObject,
    mut v_a_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
    mut v_a_1908_: *mut LeanObject,
    mut v_a_1909_: *mut LeanObject,
    mut v_a_1910_: *mut LeanObject,
    mut v_a_1911_: *mut LeanObject,
    mut v_a_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_setName_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1939_: u8 = 0;
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut v_a_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v_a_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1956_: u8 = 0;
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1970_: u8 = 0;
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: u8 = 0;
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1914_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1;
                lean_inc(v_stx_1904_);
                v___x_1915_ = l_Lean_Syntax_isOfKind(v_stx_1904_, v___x_1914_);
                if v___x_1915_ == 0 {
                    lean_dec(v_stx_1904_);
                    v___x_1916_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                    return v___x_1916_;
                } else {
                    v___x_1917_ = lean_unsigned_to_nat(1);
                    v_setName_1918_ = l_Lean_Syntax_getArg(v_stx_1904_, v___x_1917_);
                    v___x_1975_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__7;
                    lean_inc(v_setName_1918_);
                    v___x_1976_ = l_Lean_Syntax_isOfKind(v_setName_1918_, v___x_1975_);
                    if v___x_1976_ == 0 {
                        lean_dec(v_setName_1918_);
                        lean_dec(v_stx_1904_);
                        v___x_1977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                        return v___x_1977_;
                    } else {
                        v___x_1978_ = lean_unsigned_to_nat(2);
                        v___x_1979_ = l_Lean_Syntax_getArg(v_stx_1904_, v___x_1978_);
                        lean_dec(v_stx_1904_);
                        v___x_1980_ = l_Lean_Syntax_isNone(v___x_1979_);
                        if v___x_1980_ == 0 {
                            lean_inc(v___x_1979_);
                            v___x_1981_ = l_Lean_Syntax_matchesNull(v___x_1979_, v___x_1978_);
                            if v___x_1981_ == 0 {
                                lean_dec(v___x_1979_);
                                lean_dec(v_setName_1918_);
                                v___x_1982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                                return v___x_1982_;
                            } else {
                                v_d_x3f_1983_ = l_Lean_Syntax_getArg(v___x_1979_, v___x_1917_);
                                lean_dec(v___x_1979_);
                                v___x_1984_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1984_, 0, v_d_x3f_1983_);
                                v_d_x3f_1920_ = v___x_1984_;
                                v___y_1921_ = v_a_1905_;
                                v___y_1922_ = v_a_1906_;
                                v___y_1923_ = v_a_1907_;
                                v___y_1924_ = v_a_1908_;
                                v___y_1925_ = v_a_1909_;
                                v___y_1926_ = v_a_1910_;
                                v___y_1927_ = v_a_1911_;
                                v___y_1928_ = v_a_1912_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_1979_);
                            v___x_1985_ = lean_box(0);
                            v_d_x3f_1920_ = v___x_1985_;
                            v___y_1921_ = v_a_1905_;
                            v___y_1922_ = v_a_1906_;
                            v___y_1923_ = v_a_1907_;
                            v___y_1924_ = v_a_1908_;
                            v___y_1925_ = v_a_1909_;
                            v___y_1926_ = v_a_1910_;
                            v___y_1927_ = v_a_1911_;
                            v___y_1928_ = v_a_1912_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1929_ = l_Lean_TSyntax_getId(v_setName_1918_);
                v___x_1930_ = l_Lean_Meta_Sym_Simp_getSymSimpExtension_x3f(
                    v___x_1929_,
                    v___y_1927_,
                    v___y_1928_,
                );
                lean_dec(v___x_1929_);
                if lean_obj_tag(v___x_1930_) == 0 {
                    v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
                    lean_inc(v_a_1931_);
                    lean_dec_ref_known(v___x_1930_, 1);
                    if lean_obj_tag(v_a_1931_) == 1 {
                        lean_dec(v_setName_1918_);
                        v_val_1932_ = lean_ctor_get(v_a_1931_, 0);
                        lean_inc(v_val_1932_);
                        lean_dec_ref_known(v_a_1931_, 1);
                        v___x_1933_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(
                            v_val_1932_,
                            v___y_1928_,
                        );
                        lean_dec(v_val_1932_);
                        if lean_obj_tag(v___x_1933_) == 0 {
                            v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
                            lean_inc(v_a_1934_);
                            lean_dec_ref_known(v___x_1933_, 1);
                            v___x_1935_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger(v_d_x3f_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
                            if lean_obj_tag(v___x_1935_) == 0 {
                                v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
                                v_isSharedCheck_1944_ = (!lean_is_exclusive(v___x_1935_)) as u8;
                                if v_isSharedCheck_1944_ == 0 {
                                    v___x_1938_ = v___x_1935_;
                                    v_isShared_1939_ = v_isSharedCheck_1944_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_1936_);
                                    lean_dec(v___x_1935_);
                                    v___x_1938_ = lean_box(0);
                                    v_isShared_1939_ = v_isSharedCheck_1944_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_1934_);
                                v_a_1945_ = lean_ctor_get(v___x_1935_, 0);
                                v_isSharedCheck_1952_ = (!lean_is_exclusive(v___x_1935_)) as u8;
                                if v_isSharedCheck_1952_ == 0 {
                                    v___x_1947_ = v___x_1935_;
                                    v_isShared_1948_ = v_isSharedCheck_1952_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_1945_);
                                    lean_dec(v___x_1935_);
                                    v___x_1947_ = lean_box(0);
                                    v_isShared_1948_ = v_isSharedCheck_1952_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_d_x3f_1920_);
                            v_a_1953_ = lean_ctor_get(v___x_1933_, 0);
                            v_isSharedCheck_1960_ = (!lean_is_exclusive(v___x_1933_)) as u8;
                            if v_isSharedCheck_1960_ == 0 {
                                v___x_1955_ = v___x_1933_;
                                v_isShared_1956_ = v_isSharedCheck_1960_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1953_);
                                lean_dec(v___x_1933_);
                                v___x_1955_ = lean_box(0);
                                v_isShared_1956_ = v_isSharedCheck_1960_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1931_);
                        lean_dec(v_d_x3f_1920_);
                        v___x_1961_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3_once), _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3);
                        lean_inc(v_setName_1918_);
                        v___x_1962_ = l_Lean_MessageData_ofSyntax(v_setName_1918_);
                        v___x_1963_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1963_, 0, v___x_1961_);
                        lean_ctor_set(v___x_1963_, 1, v___x_1962_);
                        v___x_1964_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5_once), _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5);
                        v___x_1965_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1965_, 0, v___x_1963_);
                        lean_ctor_set(v___x_1965_, 1, v___x_1964_);
                        v___x_1966_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___redArg(v_setName_1918_, v___x_1965_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
                        lean_dec(v_setName_1918_);
                        return v___x_1966_;
                    }
                } else {
                    lean_dec(v_d_x3f_1920_);
                    lean_dec(v_setName_1918_);
                    v_a_1967_ = lean_ctor_get(v___x_1930_, 0);
                    v_isSharedCheck_1974_ = (!lean_is_exclusive(v___x_1930_)) as u8;
                    if v_isSharedCheck_1974_ == 0 {
                        v___x_1969_ = v___x_1930_;
                        v_isShared_1970_ = v_isSharedCheck_1974_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1967_);
                        lean_dec(v___x_1930_);
                        v___x_1969_ = lean_box(0);
                        v_isShared_1970_ = v_isSharedCheck_1974_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1940_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed as *mut core::ffi::c_void,
                    13,
                    2,
                );
                lean_closure_set(v___x_1940_, 0, v_a_1934_);
                lean_closure_set(v___x_1940_, 1, v_a_1936_);
                if v_isShared_1939_ == 0 {
                    lean_ctor_set(v___x_1938_, 0, v___x_1940_);
                    v___x_1942_ = v___x_1938_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
                    v___x_1942_ = v_reuseFailAlloc_1943_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1942_;
            }
            4 => {
                if v_isShared_1948_ == 0 {
                    v___x_1950_ = v___x_1947_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
                    v___x_1950_ = v_reuseFailAlloc_1951_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1950_;
            }
            6 => {
                if v_isShared_1956_ == 0 {
                    v___x_1958_ = v___x_1955_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
                    v___x_1958_ = v_reuseFailAlloc_1959_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1958_;
            }
            8 => {
                if v_isShared_1970_ == 0 {
                    v___x_1972_ = v___x_1969_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
                    v___x_1972_ = v_reuseFailAlloc_1973_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1972_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___boxed(
    mut v_stx_1986_: *mut LeanObject,
    mut v_a_1987_: *mut LeanObject,
    mut v_a_1988_: *mut LeanObject,
    mut v_a_1989_: *mut LeanObject,
    mut v_a_1990_: *mut LeanObject,
    mut v_a_1991_: *mut LeanObject,
    mut v_a_1992_: *mut LeanObject,
    mut v_a_1993_: *mut LeanObject,
    mut v_a_1994_: *mut LeanObject,
    mut v_a_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1996_: *mut LeanObject = core::ptr::null_mut();
    v_res_1996_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet(v_stx_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
    lean_dec(v_a_1994_);
    lean_dec_ref(v_a_1993_);
    lean_dec(v_a_1992_);
    lean_dec_ref(v_a_1991_);
    lean_dec(v_a_1990_);
    lean_dec_ref(v_a_1989_);
    lean_dec(v_a_1988_);
    lean_dec_ref(v_a_1987_);
    return v_res_1996_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1(
    mut v_00_u03b1_1997_: *mut LeanObject,
    mut v_ref_1998_: *mut LeanObject,
    mut v_msg_1999_: *mut LeanObject,
    mut v___y_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    v___x_2009_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___redArg(v_ref_1998_, v_msg_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
    return v___x_2009_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___boxed(
    mut v_00_u03b1_2010_: *mut LeanObject,
    mut v_ref_2011_: *mut LeanObject,
    mut v_msg_2012_: *mut LeanObject,
    mut v___y_2013_: *mut LeanObject,
    mut v___y_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
    mut v___y_2018_: *mut LeanObject,
    mut v___y_2019_: *mut LeanObject,
    mut v___y_2020_: *mut LeanObject,
    mut v___y_2021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2022_: *mut LeanObject = core::ptr::null_mut();
    v_res_2022_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1(v_00_u03b1_2010_, v_ref_2011_, v_msg_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
    lean_dec(v___y_2020_);
    lean_dec_ref(v___y_2019_);
    lean_dec(v___y_2018_);
    lean_dec_ref(v___y_2017_);
    lean_dec(v___y_2016_);
    lean_dec_ref(v___y_2015_);
    lean_dec(v___y_2014_);
    lean_dec_ref(v___y_2013_);
    lean_dec(v_ref_2011_);
    return v_res_2022_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1(
    mut v_00_u03b1_2023_: *mut LeanObject,
    mut v_msg_2024_: *mut LeanObject,
    mut v___y_2025_: *mut LeanObject,
    mut v___y_2026_: *mut LeanObject,
    mut v___y_2027_: *mut LeanObject,
    mut v___y_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
    mut v___y_2030_: *mut LeanObject,
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___redArg(v_msg_2024_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
    return v___x_2034_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___boxed(
    mut v_00_u03b1_2035_: *mut LeanObject,
    mut v_msg_2036_: *mut LeanObject,
    mut v___y_2037_: *mut LeanObject,
    mut v___y_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
    mut v___y_2042_: *mut LeanObject,
    mut v___y_2043_: *mut LeanObject,
    mut v___y_2044_: *mut LeanObject,
    mut v___y_2045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2046_: *mut LeanObject = core::ptr::null_mut();
    v_res_2046_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1(v_00_u03b1_2035_, v_msg_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
    lean_dec(v___y_2044_);
    lean_dec_ref(v___y_2043_);
    lean_dec(v___y_2042_);
    lean_dec_ref(v___y_2041_);
    lean_dec(v___y_2040_);
    lean_dec_ref(v___y_2039_);
    lean_dec(v___y_2038_);
    lean_dec_ref(v___y_2037_);
    return v_res_2046_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1()
-> *mut LeanObject {
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    v___x_2052_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_2053_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1;
    v___x_2054_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__1;
    v___x_2055_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2056_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2052_,
        v___x_2053_,
        v___x_2054_,
        v___x_2055_,
    );
    return v___x_2056_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___boxed(
    mut v_a_2057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2058_: *mut LeanObject = core::ptr::null_mut();
    v_res_2058_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1();
    return v_res_2058_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___redArg(
    mut v_as_2059_: *mut LeanObject,
    mut v_sz_2060_: usize,
    mut v_i_2061_: usize,
    mut v_b_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
    mut v___y_2065_: *mut LeanObject,
    mut v___y_2066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: usize = 0;
    let mut v___x_2077_: usize = 0;
    let mut v_a_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2082_: u8 = 0;
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2086_: u8 = 0;
    let mut v_a_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2068_ = lean_usize_dec_lt(v_i_2061_, v_sz_2060_);
                if v___x_2068_ == 0 {
                    v___x_2069_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2069_, 0, v_b_2062_);
                    return v___x_2069_;
                } else {
                    v_a_2070_ = lean_array_uget_borrowed(v_as_2059_, v_i_2061_);
                    lean_inc(v_a_2070_);
                    v___x_2071_ =
                        l_Lean_realizeGlobalConstNoOverload(v_a_2070_, v___y_2065_, v___y_2066_);
                    if lean_obj_tag(v___x_2071_) == 0 {
                        v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
                        lean_inc(v_a_2072_);
                        lean_dec_ref_known(v___x_2071_, 1);
                        v___x_2073_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(
                            v_a_2072_,
                            v___y_2063_,
                            v___y_2064_,
                            v___y_2065_,
                            v___y_2066_,
                        );
                        if lean_obj_tag(v___x_2073_) == 0 {
                            v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
                            lean_inc(v_a_2074_);
                            lean_dec_ref_known(v___x_2073_, 1);
                            v___x_2075_ =
                                l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_2062_, v_a_2074_);
                            v___x_2076_ = 1usize;
                            v___x_2077_ = lean_usize_add(v_i_2061_, v___x_2076_);
                            v_i_2061_ = v___x_2077_;
                            v_b_2062_ = v___x_2075_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_b_2062_);
                            v_a_2079_ = lean_ctor_get(v___x_2073_, 0);
                            v_isSharedCheck_2086_ = (!lean_is_exclusive(v___x_2073_)) as u8;
                            if v_isSharedCheck_2086_ == 0 {
                                v___x_2081_ = v___x_2073_;
                                v_isShared_2082_ = v_isSharedCheck_2086_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2079_);
                                lean_dec(v___x_2073_);
                                v___x_2081_ = lean_box(0);
                                v_isShared_2082_ = v_isSharedCheck_2086_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_2062_);
                        v_a_2087_ = lean_ctor_get(v___x_2071_, 0);
                        v_isSharedCheck_2094_ = (!lean_is_exclusive(v___x_2071_)) as u8;
                        if v_isSharedCheck_2094_ == 0 {
                            v___x_2089_ = v___x_2071_;
                            v_isShared_2090_ = v_isSharedCheck_2094_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2087_);
                            lean_dec(v___x_2071_);
                            v___x_2089_ = lean_box(0);
                            v_isShared_2090_ = v_isSharedCheck_2094_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2082_ == 0 {
                    v___x_2084_ = v___x_2081_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
                    v___x_2084_ = v_reuseFailAlloc_2085_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2084_;
            }
            3 => {
                if v_isShared_2090_ == 0 {
                    v___x_2092_ = v___x_2089_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
                    v___x_2092_ = v_reuseFailAlloc_2093_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___redArg___boxed(
    mut v_as_2095_: *mut LeanObject,
    mut v_sz_2096_: *mut LeanObject,
    mut v_i_2097_: *mut LeanObject,
    mut v_b_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
    mut v___y_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2104_: usize = 0;
    let mut v_i_boxed_2105_: usize = 0;
    let mut v_res_2106_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2104_ = lean_unbox_usize(v_sz_2096_);
    lean_dec(v_sz_2096_);
    v_i_boxed_2105_ = lean_unbox_usize(v_i_2097_);
    lean_dec(v_i_2097_);
    v_res_2106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___redArg(v_as_2095_, v_sz_boxed_2104_, v_i_boxed_2105_, v_b_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
    lean_dec(v___y_2102_);
    lean_dec_ref(v___y_2101_);
    lean_dec(v___y_2100_);
    lean_dec_ref(v___y_2099_);
    lean_dec_ref(v_as_2095_);
    return v_res_2106_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__2(
    mut v___x_2107_: u8,
    mut v_as_2108_: *mut LeanObject,
    mut v_i_2109_: usize,
    mut v_stop_2110_: usize,
    mut v_b_2111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: usize = 0;
    let mut v___x_2115_: usize = 0;
    let mut v___x_2117_: u8 = 0;
    let mut v_fst_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: u8 = 0;
    let mut v_snd_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2128_: u8 = 0;
    let mut v_unused_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut v_unused_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2117_ = lean_usize_dec_eq(v_i_2109_, v_stop_2110_);
                if v___x_2117_ == 0 {
                    v_fst_2118_ = lean_ctor_get(v_b_2111_, 0);
                    v___x_2119_ = (lean_unbox(v_fst_2118_) as u8);
                    if v___x_2119_ == 0 {
                        v_snd_2120_ = lean_ctor_get(v_b_2111_, 1);
                        v_isSharedCheck_2128_ = (!lean_is_exclusive(v_b_2111_)) as u8;
                        if v_isSharedCheck_2128_ == 0 {
                            v_unused_2129_ = lean_ctor_get(v_b_2111_, 0);
                            lean_dec(v_unused_2129_);
                            v___x_2122_ = v_b_2111_;
                            v_isShared_2123_ = v_isSharedCheck_2128_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_2120_);
                            lean_dec(v_b_2111_);
                            v___x_2122_ = lean_box(0);
                            v_isShared_2123_ = v_isSharedCheck_2128_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_2130_ = lean_ctor_get(v_b_2111_, 1);
                        v_isSharedCheck_2140_ = (!lean_is_exclusive(v_b_2111_)) as u8;
                        if v_isSharedCheck_2140_ == 0 {
                            v_unused_2141_ = lean_ctor_get(v_b_2111_, 0);
                            lean_dec(v_unused_2141_);
                            v___x_2132_ = v_b_2111_;
                            v_isShared_2133_ = v_isSharedCheck_2140_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_snd_2130_);
                            lean_dec(v_b_2111_);
                            v___x_2132_ = lean_box(0);
                            v_isShared_2133_ = v_isSharedCheck_2140_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_2111_;
                }
            }
            1 => {
                v___x_2114_ = 1usize;
                v___x_2115_ = lean_usize_add(v_i_2109_, v___x_2114_);
                v_i_2109_ = v___x_2115_;
                v_b_2111_ = v___y_2113_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2124_ = lean_box((v___x_2107_) as usize);
                if v_isShared_2123_ == 0 {
                    lean_ctor_set(v___x_2122_, 0, v___x_2124_);
                    v___x_2126_ = v___x_2122_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
                    lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_snd_2120_);
                    v___x_2126_ = v_reuseFailAlloc_2127_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_2113_ = v___x_2126_;
                state = 1;
                continue;
            }
            4 => {
                v___x_2134_ = lean_array_uget_borrowed(v_as_2108_, v_i_2109_);
                lean_inc(v___x_2134_);
                v___x_2135_ = lean_array_push(v_snd_2130_, v___x_2134_);
                v___x_2136_ = lean_box((v___x_2117_) as usize);
                if v_isShared_2133_ == 0 {
                    lean_ctor_set(v___x_2132_, 1, v___x_2135_);
                    lean_ctor_set(v___x_2132_, 0, v___x_2136_);
                    v___x_2138_ = v___x_2132_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
                    lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2135_);
                    v___x_2138_ = v_reuseFailAlloc_2139_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2113_ = v___x_2138_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__2___boxed(
    mut v___x_2142_: *mut LeanObject,
    mut v_as_2143_: *mut LeanObject,
    mut v_i_2144_: *mut LeanObject,
    mut v_stop_2145_: *mut LeanObject,
    mut v_b_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2743__boxed_2147_: u8 = 0;
    let mut v_i_boxed_2148_: usize = 0;
    let mut v_stop_boxed_2149_: usize = 0;
    let mut v_res_2150_: *mut LeanObject = core::ptr::null_mut();
    v___x_2743__boxed_2147_ = (lean_unbox(v___x_2142_) as u8);
    v_i_boxed_2148_ = lean_unbox_usize(v_i_2144_);
    lean_dec(v_i_2144_);
    v_stop_boxed_2149_ = lean_unbox_usize(v_stop_2145_);
    lean_dec(v_stop_2145_);
    v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__2(v___x_2743__boxed_2147_, v_as_2143_, v_i_boxed_2148_, v_stop_boxed_2149_, v_b_2146_);
    lean_dec_ref(v_as_2143_);
    return v_res_2150_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__0(
    mut v_sz_2151_: usize,
    mut v_i_2152_: usize,
    mut v_bs_2153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: usize = 0;
    let mut v___x_2163_: usize = 0;
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2154_ = lean_usize_dec_lt(v_i_2152_, v_sz_2151_);
                if v___x_2154_ == 0 {
                    v___x_2155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2155_, 0, v_bs_2153_);
                    return v___x_2155_;
                } else {
                    v_v_2156_ = lean_array_uget(v_bs_2153_, v_i_2152_);
                    v___x_2157_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__7;
                    lean_inc(v_v_2156_);
                    v___x_2158_ = l_Lean_Syntax_isOfKind(v_v_2156_, v___x_2157_);
                    if v___x_2158_ == 0 {
                        lean_dec(v_v_2156_);
                        lean_dec_ref(v_bs_2153_);
                        v___x_2159_ = lean_box(0);
                        return v___x_2159_;
                    } else {
                        v___x_2160_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2161_ = lean_array_uset(v_bs_2153_, v_i_2152_, v___x_2160_);
                        v___x_2162_ = 1usize;
                        v___x_2163_ = lean_usize_add(v_i_2152_, v___x_2162_);
                        v___x_2164_ = lean_array_uset(v_bs_x27_2161_, v_i_2152_, v_v_2156_);
                        v_i_2152_ = v___x_2163_;
                        v_bs_2153_ = v___x_2164_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__0___boxed(
    mut v_sz_2166_: *mut LeanObject,
    mut v_i_2167_: *mut LeanObject,
    mut v_bs_2168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2169_: usize = 0;
    let mut v_i_boxed_2170_: usize = 0;
    let mut v_res_2171_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2169_ = lean_unbox_usize(v_sz_2166_);
    lean_dec(v_sz_2166_);
    v_i_boxed_2170_ = lean_unbox_usize(v_i_2167_);
    lean_dec(v_i_2167_);
    v_res_2171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__0(v_sz_boxed_2169_, v_i_boxed_2170_, v_bs_2168_);
    return v_res_2171_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0()
-> *mut LeanObject {
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    v___x_2172_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2172_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1()
-> *mut LeanObject {
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thms_2174_: *mut LeanObject = core::ptr::null_mut();
    v___x_2173_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0_once), _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0);
    v_thms_2174_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v_thms_2174_, 0, v___x_2173_);
    return v_thms_2174_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline(
    mut v_stx_2184_: *mut LeanObject,
    mut v_a_2185_: *mut LeanObject,
    mut v_a_2186_: *mut LeanObject,
    mut v_a_2187_: *mut LeanObject,
    mut v_a_2188_: *mut LeanObject,
    mut v_a_2189_: *mut LeanObject,
    mut v_a_2190_: *mut LeanObject,
    mut v_a_2191_: *mut LeanObject,
    mut v_a_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2195_: usize = 0;
    let mut v___y_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thms_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2207_: usize = 0;
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2214_: u8 = 0;
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2219_: u8 = 0;
    let mut v_a_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2227_: u8 = 0;
    let mut v_a_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2243_: usize = 0;
    let mut v___x_2244_: usize = 0;
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u8 = 0;
    let mut v___x_2254_: u8 = 0;
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: u8 = 0;
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2271_: usize = 0;
    let mut v___x_2272_: usize = 0;
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: usize = 0;
    let mut v___x_2276_: usize = 0;
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2236_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3;
                lean_inc(v_stx_2184_);
                v___x_2237_ = l_Lean_Syntax_isOfKind(v_stx_2184_, v___x_2236_);
                if v___x_2237_ == 0 {
                    lean_dec(v_stx_2184_);
                    v___x_2238_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                    return v___x_2238_;
                } else {
                    v___x_2239_ = lean_unsigned_to_nat(1);
                    v___x_2240_ = lean_unsigned_to_nat(2);
                    v___x_2262_ = l_Lean_Syntax_getArg(v_stx_2184_, v___x_2240_);
                    v___x_2263_ = l_Lean_Syntax_getArgs(v___x_2262_);
                    lean_dec(v___x_2262_);
                    v___x_2264_ = lean_unsigned_to_nat(0);
                    v___x_2265_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__4;
                    v___x_2266_ = lean_array_get_size(v___x_2263_);
                    v___x_2267_ = lean_nat_dec_lt(v___x_2264_, v___x_2266_);
                    if v___x_2267_ == 0 {
                        lean_dec_ref(v___x_2263_);
                        v___y_2242_ = v___x_2265_;
                        state = 8;
                        continue;
                    } else {
                        v___x_2268_ = lean_box((v___x_2237_) as usize);
                        v___x_2269_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2269_, 0, v___x_2268_);
                        lean_ctor_set(v___x_2269_, 1, v___x_2265_);
                        v___x_2270_ = lean_nat_dec_le(v___x_2266_, v___x_2266_);
                        if v___x_2270_ == 0 {
                            if v___x_2267_ == 0 {
                                lean_dec_ref_known(v___x_2269_, 2);
                                lean_dec_ref(v___x_2263_);
                                v___y_2242_ = v___x_2265_;
                                state = 8;
                                continue;
                            } else {
                                v___x_2271_ = 0usize;
                                v___x_2272_ = lean_usize_of_nat(v___x_2266_);
                                v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__2(v___x_2237_, v___x_2263_, v___x_2271_, v___x_2272_, v___x_2269_);
                                lean_dec_ref(v___x_2263_);
                                v_snd_2274_ = lean_ctor_get(v___x_2273_, 1);
                                lean_inc(v_snd_2274_);
                                lean_dec_ref(v___x_2273_);
                                v___y_2242_ = v_snd_2274_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___x_2275_ = 0usize;
                            v___x_2276_ = lean_usize_of_nat(v___x_2266_);
                            v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__2(v___x_2237_, v___x_2263_, v___x_2275_, v___x_2276_, v___x_2269_);
                            lean_dec_ref(v___x_2263_);
                            v_snd_2278_ = lean_ctor_get(v___x_2277_, 1);
                            lean_inc(v_snd_2278_);
                            lean_dec_ref(v___x_2277_);
                            v___y_2242_ = v_snd_2278_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_thms_2206_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1_once), _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1);
                v_sz_2207_ = lean_array_size(v___y_2196_);
                v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___redArg(v___y_2196_, v_sz_2207_, v___y_2195_, v_thms_2206_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
                lean_dec_ref(v___y_2196_);
                if lean_obj_tag(v___x_2208_) == 0 {
                    v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
                    lean_inc(v_a_2209_);
                    lean_dec_ref_known(v___x_2208_, 1);
                    v___x_2210_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger(v_d_x3f_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
                    if lean_obj_tag(v___x_2210_) == 0 {
                        v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2219_ = (!lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2219_ == 0 {
                            v___x_2213_ = v___x_2210_;
                            v_isShared_2214_ = v_isSharedCheck_2219_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2211_);
                            lean_dec(v___x_2210_);
                            v___x_2213_ = lean_box(0);
                            v_isShared_2214_ = v_isSharedCheck_2219_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2209_);
                        v_a_2220_ = lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2227_ = (!lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2227_ == 0 {
                            v___x_2222_ = v___x_2210_;
                            v_isShared_2223_ = v_isSharedCheck_2227_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2220_);
                            lean_dec(v___x_2210_);
                            v___x_2222_ = lean_box(0);
                            v_isShared_2223_ = v_isSharedCheck_2227_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_d_x3f_2197_);
                    v_a_2228_ = lean_ctor_get(v___x_2208_, 0);
                    v_isSharedCheck_2235_ = (!lean_is_exclusive(v___x_2208_)) as u8;
                    if v_isSharedCheck_2235_ == 0 {
                        v___x_2230_ = v___x_2208_;
                        v_isShared_2231_ = v_isSharedCheck_2235_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2228_);
                        lean_dec(v___x_2208_);
                        v___x_2230_ = lean_box(0);
                        v_isShared_2231_ = v_isSharedCheck_2235_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2215_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed as *mut core::ffi::c_void,
                    13,
                    2,
                );
                lean_closure_set(v___x_2215_, 0, v_a_2209_);
                lean_closure_set(v___x_2215_, 1, v_a_2211_);
                if v_isShared_2214_ == 0 {
                    lean_ctor_set(v___x_2213_, 0, v___x_2215_);
                    v___x_2217_ = v___x_2213_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
                    v___x_2217_ = v_reuseFailAlloc_2218_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2217_;
            }
            4 => {
                if v_isShared_2223_ == 0 {
                    v___x_2225_ = v___x_2222_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
                    v___x_2225_ = v_reuseFailAlloc_2226_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2225_;
            }
            6 => {
                if v_isShared_2231_ == 0 {
                    v___x_2233_ = v___x_2230_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
                    v___x_2233_ = v_reuseFailAlloc_2234_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2233_;
            }
            8 => {
                v_sz_2243_ = lean_array_size(v___y_2242_);
                v___x_2244_ = 0usize;
                v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__0(v_sz_2243_, v___x_2244_, v___y_2242_);
                if lean_obj_tag(v___x_2245_) == 0 {
                    lean_dec(v_stx_2184_);
                    v___x_2246_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                    return v___x_2246_;
                } else {
                    v_val_2247_ = lean_ctor_get(v___x_2245_, 0);
                    v_isSharedCheck_2261_ = (!lean_is_exclusive(v___x_2245_)) as u8;
                    if v_isSharedCheck_2261_ == 0 {
                        v___x_2249_ = v___x_2245_;
                        v_isShared_2250_ = v_isSharedCheck_2261_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_val_2247_);
                        lean_dec(v___x_2245_);
                        v___x_2249_ = lean_box(0);
                        v_isShared_2250_ = v_isSharedCheck_2261_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2251_ = lean_unsigned_to_nat(4);
                v___x_2252_ = l_Lean_Syntax_getArg(v_stx_2184_, v___x_2251_);
                lean_dec(v_stx_2184_);
                v___x_2253_ = l_Lean_Syntax_isNone(v___x_2252_);
                if v___x_2253_ == 0 {
                    lean_inc(v___x_2252_);
                    v___x_2254_ = l_Lean_Syntax_matchesNull(v___x_2252_, v___x_2240_);
                    if v___x_2254_ == 0 {
                        lean_dec(v___x_2252_);
                        lean_del_object(v___x_2249_);
                        lean_dec(v_val_2247_);
                        v___x_2255_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                        return v___x_2255_;
                    } else {
                        v_d_x3f_2256_ = l_Lean_Syntax_getArg(v___x_2252_, v___x_2239_);
                        lean_dec(v___x_2252_);
                        if v_isShared_2250_ == 0 {
                            lean_ctor_set(v___x_2249_, 0, v_d_x3f_2256_);
                            v___x_2258_ = v___x_2249_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_d_x3f_2256_);
                            v___x_2258_ = v_reuseFailAlloc_2259_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2252_);
                    lean_del_object(v___x_2249_);
                    v___x_2260_ = lean_box(0);
                    v___y_2195_ = v___x_2244_;
                    v___y_2196_ = v_val_2247_;
                    v_d_x3f_2197_ = v___x_2260_;
                    v___y_2198_ = v_a_2185_;
                    v___y_2199_ = v_a_2186_;
                    v___y_2200_ = v_a_2187_;
                    v___y_2201_ = v_a_2188_;
                    v___y_2202_ = v_a_2189_;
                    v___y_2203_ = v_a_2190_;
                    v___y_2204_ = v_a_2191_;
                    v___y_2205_ = v_a_2192_;
                    state = 1;
                    continue;
                }
            }
            10 => {
                v___y_2195_ = v___x_2244_;
                v___y_2196_ = v_val_2247_;
                v_d_x3f_2197_ = v___x_2258_;
                v___y_2198_ = v_a_2185_;
                v___y_2199_ = v_a_2186_;
                v___y_2200_ = v_a_2187_;
                v___y_2201_ = v_a_2188_;
                v___y_2202_ = v_a_2189_;
                v___y_2203_ = v_a_2190_;
                v___y_2204_ = v_a_2191_;
                v___y_2205_ = v_a_2192_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___boxed(
    mut v_stx_2279_: *mut LeanObject,
    mut v_a_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
    mut v_a_2286_: *mut LeanObject,
    mut v_a_2287_: *mut LeanObject,
    mut v_a_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2289_: *mut LeanObject = core::ptr::null_mut();
    v_res_2289_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline(v_stx_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
    lean_dec(v_a_2287_);
    lean_dec_ref(v_a_2286_);
    lean_dec(v_a_2285_);
    lean_dec_ref(v_a_2284_);
    lean_dec(v_a_2283_);
    lean_dec_ref(v_a_2282_);
    lean_dec(v_a_2281_);
    lean_dec_ref(v_a_2280_);
    return v_res_2289_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1(
    mut v_as_2290_: *mut LeanObject,
    mut v_sz_2291_: usize,
    mut v_i_2292_: usize,
    mut v_b_2293_: *mut LeanObject,
    mut v___y_2294_: *mut LeanObject,
    mut v___y_2295_: *mut LeanObject,
    mut v___y_2296_: *mut LeanObject,
    mut v___y_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___redArg(v_as_2290_, v_sz_2291_, v_i_2292_, v_b_2293_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
    return v___x_2303_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___boxed(
    mut v_as_2304_: *mut LeanObject,
    mut v_sz_2305_: *mut LeanObject,
    mut v_i_2306_: *mut LeanObject,
    mut v_b_2307_: *mut LeanObject,
    mut v___y_2308_: *mut LeanObject,
    mut v___y_2309_: *mut LeanObject,
    mut v___y_2310_: *mut LeanObject,
    mut v___y_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2317_: usize = 0;
    let mut v_i_boxed_2318_: usize = 0;
    let mut v_res_2319_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2317_ = lean_unbox_usize(v_sz_2305_);
    lean_dec(v_sz_2305_);
    v_i_boxed_2318_ = lean_unbox_usize(v_i_2306_);
    lean_dec(v_i_2306_);
    v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1(v_as_2304_, v_sz_boxed_2317_, v_i_boxed_2318_, v_b_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
    lean_dec(v___y_2315_);
    lean_dec_ref(v___y_2314_);
    lean_dec(v___y_2313_);
    lean_dec_ref(v___y_2312_);
    lean_dec(v___y_2311_);
    lean_dec_ref(v___y_2310_);
    lean_dec(v___y_2309_);
    lean_dec_ref(v___y_2308_);
    lean_dec_ref(v_as_2304_);
    return v_res_2319_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1()
-> *mut LeanObject {
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    v___x_2325_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_2326_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3;
    v___x_2327_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__1;
    v___x_2328_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2329_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2325_,
        v___x_2326_,
        v___x_2327_,
        v___x_2328_,
    );
    return v___x_2329_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___boxed(
    mut v_a_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2331_: *mut LeanObject = core::ptr::null_mut();
    v_res_2331_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1();
    return v_res_2331_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___lam__0(
    mut v_a_2332_: *mut LeanObject,
    mut v_a_2333_: *mut LeanObject,
    mut v___y_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_2347_: u8 = 0;
    let mut v_contextDependent_2348_: u8 = 0;
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2352_: u8 = 0;
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_unused_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2362_: u8 = 0;
    let mut v_contextDependent_2363_: u8 = 0;
    let mut v_done_2364_: u8 = 0;
    let mut v_e_x27_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2367_: u8 = 0;
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2370_: u8 = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v_done_2376_: u8 = 0;
    let mut v_contextDependent_2377_: u8 = 0;
    let mut v___y_2379_: u8 = 0;
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_2388_: u8 = 0;
    let mut v_contextDependent_2389_: u8 = 0;
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2397_: u8 = 0;
    let mut v___y_2399_: u8 = 0;
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut v_a_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2410_: u8 = 0;
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2414_: u8 = 0;
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2343_);
                lean_inc_ref(v___y_2342_);
                lean_inc(v___y_2341_);
                lean_inc_ref(v___y_2340_);
                lean_inc(v___y_2339_);
                lean_inc_ref(v___y_2338_);
                lean_inc(v___y_2337_);
                lean_inc_ref(v___y_2336_);
                lean_inc(v___y_2335_);
                lean_inc_ref(v___y_2334_);
                v___x_2345_ = lean_apply_11(
                    v_a_2332_,
                    v___y_2334_,
                    v___y_2335_,
                    v___y_2336_,
                    v___y_2337_,
                    v___y_2338_,
                    v___y_2339_,
                    v___y_2340_,
                    v___y_2341_,
                    v___y_2342_,
                    v___y_2343_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2345_) == 0 {
                    v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
                    lean_inc(v_a_2346_);
                    if lean_obj_tag(v_a_2346_) == 0 {
                        v_done_2347_ = lean_ctor_get_uint8(v_a_2346_, 0 as u32);
                        if v_done_2347_ == 0 {
                            lean_dec_ref_known(v___x_2345_, 1);
                            v_contextDependent_2348_ = lean_ctor_get_uint8(v_a_2346_, 1 as u32);
                            lean_dec_ref_known(v_a_2346_, 0);
                            v___x_2349_ = lean_apply_11(
                                v_a_2333_,
                                v___y_2334_,
                                v___y_2335_,
                                v___y_2336_,
                                v___y_2337_,
                                v___y_2338_,
                                v___y_2339_,
                                v___y_2340_,
                                v___y_2341_,
                                v___y_2342_,
                                v___y_2343_,
                                lean_box(0),
                            );
                            if lean_obj_tag(v___x_2349_) == 0 {
                                v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
                                lean_inc(v_a_2350_);
                                if v_contextDependent_2348_ == 0 {
                                    lean_dec(v_a_2350_);
                                    return v___x_2349_;
                                } else {
                                    if lean_obj_tag(v_a_2350_) == 0 {
                                        v_contextDependent_2362_ =
                                            lean_ctor_get_uint8(v_a_2350_, 1 as u32);
                                        v___y_2352_ = v_contextDependent_2362_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_contextDependent_2363_ = lean_ctor_get_uint8(
                                            v_a_2350_,
                                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1)
                                                as u32,
                                        );
                                        v___y_2352_ = v_contextDependent_2363_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                return v___x_2349_;
                            }
                        } else {
                            lean_dec_ref_known(v_a_2346_, 0);
                            lean_dec(v___y_2343_);
                            lean_dec_ref(v___y_2342_);
                            lean_dec(v___y_2341_);
                            lean_dec_ref(v___y_2340_);
                            lean_dec(v___y_2339_);
                            lean_dec_ref(v___y_2338_);
                            lean_dec(v___y_2337_);
                            lean_dec_ref(v___y_2336_);
                            lean_dec(v___y_2335_);
                            lean_dec_ref(v___y_2334_);
                            lean_dec_ref(v_a_2333_);
                            return v___x_2345_;
                        }
                    } else {
                        v_done_2364_ = lean_ctor_get_uint8(
                            v_a_2346_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        if v_done_2364_ == 0 {
                            lean_dec_ref_known(v___x_2345_, 1);
                            v_e_x27_2365_ = lean_ctor_get(v_a_2346_, 0);
                            v_proof_2366_ = lean_ctor_get(v_a_2346_, 1);
                            v_contextDependent_2367_ = lean_ctor_get_uint8(
                                v_a_2346_,
                                (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                            );
                            v_isSharedCheck_2417_ = (!lean_is_exclusive(v_a_2346_)) as u8;
                            if v_isSharedCheck_2417_ == 0 {
                                v___x_2369_ = v_a_2346_;
                                v_isShared_2370_ = v_isSharedCheck_2417_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_proof_2366_);
                                lean_inc(v_e_x27_2365_);
                                lean_dec(v_a_2346_);
                                v___x_2369_ = lean_box(0);
                                v_isShared_2370_ = v_isSharedCheck_2417_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_a_2346_, 2);
                            lean_dec(v___y_2343_);
                            lean_dec_ref(v___y_2342_);
                            lean_dec(v___y_2341_);
                            lean_dec_ref(v___y_2340_);
                            lean_dec(v___y_2339_);
                            lean_dec_ref(v___y_2338_);
                            lean_dec(v___y_2337_);
                            lean_dec_ref(v___y_2336_);
                            lean_dec(v___y_2335_);
                            lean_dec_ref(v___y_2334_);
                            lean_dec_ref(v_a_2333_);
                            return v___x_2345_;
                        }
                    }
                } else {
                    lean_dec(v___y_2343_);
                    lean_dec_ref(v___y_2342_);
                    lean_dec(v___y_2341_);
                    lean_dec_ref(v___y_2340_);
                    lean_dec(v___y_2339_);
                    lean_dec_ref(v___y_2338_);
                    lean_dec(v___y_2337_);
                    lean_dec_ref(v___y_2336_);
                    lean_dec(v___y_2335_);
                    lean_dec_ref(v___y_2334_);
                    lean_dec_ref(v_a_2333_);
                    return v___x_2345_;
                }
            }
            1 => {
                if v___y_2352_ == 0 {
                    v_isSharedCheck_2360_ = (!lean_is_exclusive(v___x_2349_)) as u8;
                    if v_isSharedCheck_2360_ == 0 {
                        v_unused_2361_ = lean_ctor_get(v___x_2349_, 0);
                        lean_dec(v_unused_2361_);
                        v___x_2354_ = v___x_2349_;
                        v_isShared_2355_ = v_isSharedCheck_2360_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2349_);
                        v___x_2354_ = lean_box(0);
                        v_isShared_2355_ = v_isSharedCheck_2360_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2350_);
                    return v___x_2349_;
                }
            }
            2 => {
                v___x_2356_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2350_);
                if v_isShared_2355_ == 0 {
                    lean_ctor_set(v___x_2354_, 0, v___x_2356_);
                    v___x_2358_ = v___x_2354_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
                    v___x_2358_ = v_reuseFailAlloc_2359_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2358_;
            }
            4 => {
                lean_inc(v___y_2343_);
                lean_inc_ref(v___y_2342_);
                lean_inc(v___y_2341_);
                lean_inc_ref(v___y_2340_);
                lean_inc(v___y_2339_);
                lean_inc_ref(v_e_x27_2365_);
                v___x_2371_ = lean_apply_11(
                    v_a_2333_,
                    v_e_x27_2365_,
                    v___y_2335_,
                    v___y_2336_,
                    v___y_2337_,
                    v___y_2338_,
                    v___y_2339_,
                    v___y_2340_,
                    v___y_2341_,
                    v___y_2342_,
                    v___y_2343_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2371_) == 0 {
                    v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
                    v_isSharedCheck_2416_ = (!lean_is_exclusive(v___x_2371_)) as u8;
                    if v_isSharedCheck_2416_ == 0 {
                        v___x_2374_ = v___x_2371_;
                        v_isShared_2375_ = v_isSharedCheck_2416_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2372_);
                        lean_dec(v___x_2371_);
                        v___x_2374_ = lean_box(0);
                        v_isShared_2375_ = v_isSharedCheck_2416_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2369_);
                    lean_dec_ref(v_proof_2366_);
                    lean_dec_ref(v_e_x27_2365_);
                    lean_dec(v___y_2343_);
                    lean_dec_ref(v___y_2342_);
                    lean_dec(v___y_2341_);
                    lean_dec_ref(v___y_2340_);
                    lean_dec(v___y_2339_);
                    lean_dec_ref(v___y_2334_);
                    return v___x_2371_;
                }
            }
            5 => {
                if lean_obj_tag(v_a_2372_) == 0 {
                    lean_dec(v___y_2343_);
                    lean_dec_ref(v___y_2342_);
                    lean_dec(v___y_2341_);
                    lean_dec_ref(v___y_2340_);
                    lean_dec(v___y_2339_);
                    lean_dec_ref(v___y_2334_);
                    v_done_2376_ = lean_ctor_get_uint8(v_a_2372_, 0 as u32);
                    v_contextDependent_2377_ = lean_ctor_get_uint8(v_a_2372_, 1 as u32);
                    lean_dec_ref_known(v_a_2372_, 0);
                    if v_contextDependent_2367_ == 0 {
                        v___y_2379_ = v_contextDependent_2377_;
                        state = 6;
                        continue;
                    } else {
                        v___y_2379_ = v_contextDependent_2367_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2374_);
                    lean_del_object(v___x_2369_);
                    v_e_x27_2386_ = lean_ctor_get(v_a_2372_, 0);
                    v_proof_2387_ = lean_ctor_get(v_a_2372_, 1);
                    v_done_2388_ = lean_ctor_get_uint8(
                        v_a_2372_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_contextDependent_2389_ = lean_ctor_get_uint8(
                        v_a_2372_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_2415_ = (!lean_is_exclusive(v_a_2372_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2391_ = v_a_2372_;
                        v_isShared_2392_ = v_isSharedCheck_2415_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_proof_2387_);
                        lean_inc(v_e_x27_2386_);
                        lean_dec(v_a_2372_);
                        v___x_2391_ = lean_box(0);
                        v_isShared_2392_ = v_isSharedCheck_2415_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_2370_ == 0 {
                    v___x_2381_ = v___x_2369_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_e_x27_2365_);
                    lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_proof_2366_);
                    v___x_2381_ = v_reuseFailAlloc_2385_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_ctor_set_uint8(
                    v___x_2381_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_done_2376_,
                );
                lean_ctor_set_uint8(
                    v___x_2381_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_2379_,
                );
                if v_isShared_2375_ == 0 {
                    lean_ctor_set(v___x_2374_, 0, v___x_2381_);
                    v___x_2383_ = v___x_2374_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
                    v___x_2383_ = v_reuseFailAlloc_2384_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2383_;
            }
            9 => {
                lean_inc_ref(v_e_x27_2386_);
                v___x_2393_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
                    v___y_2334_,
                    v_e_x27_2365_,
                    v_proof_2366_,
                    v_e_x27_2386_,
                    v_proof_2387_,
                    v___y_2339_,
                    v___y_2340_,
                    v___y_2341_,
                    v___y_2342_,
                    v___y_2343_,
                );
                lean_dec(v___y_2343_);
                lean_dec_ref(v___y_2342_);
                lean_dec(v___y_2341_);
                lean_dec_ref(v___y_2340_);
                lean_dec(v___y_2339_);
                if lean_obj_tag(v___x_2393_) == 0 {
                    v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
                    v_isSharedCheck_2406_ = (!lean_is_exclusive(v___x_2393_)) as u8;
                    if v_isSharedCheck_2406_ == 0 {
                        v___x_2396_ = v___x_2393_;
                        v_isShared_2397_ = v_isSharedCheck_2406_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2394_);
                        lean_dec(v___x_2393_);
                        v___x_2396_ = lean_box(0);
                        v_isShared_2397_ = v_isSharedCheck_2406_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2391_);
                    lean_dec_ref(v_e_x27_2386_);
                    v_a_2407_ = lean_ctor_get(v___x_2393_, 0);
                    v_isSharedCheck_2414_ = (!lean_is_exclusive(v___x_2393_)) as u8;
                    if v_isSharedCheck_2414_ == 0 {
                        v___x_2409_ = v___x_2393_;
                        v_isShared_2410_ = v_isSharedCheck_2414_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2407_);
                        lean_dec(v___x_2393_);
                        v___x_2409_ = lean_box(0);
                        v_isShared_2410_ = v_isSharedCheck_2414_;
                        state = 14;
                        continue;
                    }
                }
            }
            10 => {
                if v_contextDependent_2367_ == 0 {
                    v___y_2399_ = v_contextDependent_2389_;
                    state = 11;
                    continue;
                } else {
                    v___y_2399_ = v_contextDependent_2367_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2392_ == 0 {
                    lean_ctor_set(v___x_2391_, 1, v_a_2394_);
                    v___x_2401_ = v___x_2391_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_e_x27_2386_);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_a_2394_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2405_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_done_2388_,
                    );
                    v___x_2401_ = v_reuseFailAlloc_2405_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                lean_ctor_set_uint8(
                    v___x_2401_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_2399_,
                );
                if v_isShared_2397_ == 0 {
                    lean_ctor_set(v___x_2396_, 0, v___x_2401_);
                    v___x_2403_ = v___x_2396_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
                    v___x_2403_ = v_reuseFailAlloc_2404_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2403_;
            }
            14 => {
                if v_isShared_2410_ == 0 {
                    v___x_2412_ = v___x_2409_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
                    v___x_2412_ = v_reuseFailAlloc_2413_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___lam__0___boxed(
    mut v_a_2418_: *mut LeanObject,
    mut v_a_2419_: *mut LeanObject,
    mut v___y_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
    mut v___y_2425_: *mut LeanObject,
    mut v___y_2426_: *mut LeanObject,
    mut v___y_2427_: *mut LeanObject,
    mut v___y_2428_: *mut LeanObject,
    mut v___y_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2431_: *mut LeanObject = core::ptr::null_mut();
    v_res_2431_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___lam__0(v_a_2418_, v_a_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
    return v_res_2431_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen(
    mut v_stx_2439_: *mut LeanObject,
    mut v_a_2440_: *mut LeanObject,
    mut v_a_2441_: *mut LeanObject,
    mut v_a_2442_: *mut LeanObject,
    mut v_a_2443_: *mut LeanObject,
    mut v_a_2444_: *mut LeanObject,
    mut v_a_2445_: *mut LeanObject,
    mut v_a_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2462_: u8 = 0;
    let mut v___f_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2449_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1;
                lean_inc(v_stx_2439_);
                v___x_2450_ = l_Lean_Syntax_isOfKind(v_stx_2439_, v___x_2449_);
                if v___x_2450_ == 0 {
                    lean_dec(v_stx_2439_);
                    v___x_2451_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                    return v___x_2451_;
                } else {
                    v___x_2452_ = lean_unsigned_to_nat(0);
                    v___x_2453_ = l_Lean_Syntax_getArg(v_stx_2439_, v___x_2452_);
                    v___x_2454_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(
                        v___x_2453_,
                        v_a_2440_,
                        v_a_2441_,
                        v_a_2442_,
                        v_a_2443_,
                        v_a_2444_,
                        v_a_2445_,
                        v_a_2446_,
                        v_a_2447_,
                    );
                    if lean_obj_tag(v___x_2454_) == 0 {
                        v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
                        lean_inc(v_a_2455_);
                        lean_dec_ref_known(v___x_2454_, 1);
                        v___x_2456_ = lean_unsigned_to_nat(2);
                        v___x_2457_ = l_Lean_Syntax_getArg(v_stx_2439_, v___x_2456_);
                        lean_dec(v_stx_2439_);
                        v___x_2458_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(
                            v___x_2457_,
                            v_a_2440_,
                            v_a_2441_,
                            v_a_2442_,
                            v_a_2443_,
                            v_a_2444_,
                            v_a_2445_,
                            v_a_2446_,
                            v_a_2447_,
                        );
                        if lean_obj_tag(v___x_2458_) == 0 {
                            v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
                            v_isSharedCheck_2467_ = (!lean_is_exclusive(v___x_2458_)) as u8;
                            if v_isSharedCheck_2467_ == 0 {
                                v___x_2461_ = v___x_2458_;
                                v_isShared_2462_ = v_isSharedCheck_2467_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2459_);
                                lean_dec(v___x_2458_);
                                v___x_2461_ = lean_box(0);
                                v_isShared_2462_ = v_isSharedCheck_2467_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2455_);
                            return v___x_2458_;
                        }
                    } else {
                        lean_dec(v_stx_2439_);
                        return v___x_2454_;
                    }
                }
            }
            1 => {
                v___f_2463_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                lean_closure_set(v___f_2463_, 0, v_a_2455_);
                lean_closure_set(v___f_2463_, 1, v_a_2459_);
                if v_isShared_2462_ == 0 {
                    lean_ctor_set(v___x_2461_, 0, v___f_2463_);
                    v___x_2465_ = v___x_2461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___f_2463_);
                    v___x_2465_ = v_reuseFailAlloc_2466_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___boxed(
    mut v_stx_2468_: *mut LeanObject,
    mut v_a_2469_: *mut LeanObject,
    mut v_a_2470_: *mut LeanObject,
    mut v_a_2471_: *mut LeanObject,
    mut v_a_2472_: *mut LeanObject,
    mut v_a_2473_: *mut LeanObject,
    mut v_a_2474_: *mut LeanObject,
    mut v_a_2475_: *mut LeanObject,
    mut v_a_2476_: *mut LeanObject,
    mut v_a_2477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2478_: *mut LeanObject = core::ptr::null_mut();
    v_res_2478_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen(v_stx_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
    lean_dec(v_a_2476_);
    lean_dec_ref(v_a_2475_);
    lean_dec(v_a_2474_);
    lean_dec_ref(v_a_2473_);
    lean_dec(v_a_2472_);
    lean_dec_ref(v_a_2471_);
    lean_dec(v_a_2470_);
    lean_dec_ref(v_a_2469_);
    return v_res_2478_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1()
-> *mut LeanObject {
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    v___x_2484_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_2485_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1;
    v___x_2486_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__1;
    v___x_2487_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2488_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2484_,
        v___x_2485_,
        v___x_2486_,
        v___x_2487_,
    );
    return v___x_2488_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___boxed(
    mut v_a_2489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2490_: *mut LeanObject = core::ptr::null_mut();
    v_res_2490_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1();
    return v_res_2490_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___lam__0(
    mut v_a_2491_: *mut LeanObject,
    mut v_a_2492_: *mut LeanObject,
    mut v___y_2493_: *mut LeanObject,
    mut v___y_2494_: *mut LeanObject,
    mut v___y_2495_: *mut LeanObject,
    mut v___y_2496_: *mut LeanObject,
    mut v___y_2497_: *mut LeanObject,
    mut v___y_2498_: *mut LeanObject,
    mut v___y_2499_: *mut LeanObject,
    mut v___y_2500_: *mut LeanObject,
    mut v___y_2501_: *mut LeanObject,
    mut v___y_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_2506_: u8 = 0;
    let mut v_contextDependent_2507_: u8 = 0;
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2511_: u8 = 0;
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2519_: u8 = 0;
    let mut v_unused_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2521_: u8 = 0;
    let mut v_contextDependent_2522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2502_);
                lean_inc_ref(v___y_2501_);
                lean_inc(v___y_2500_);
                lean_inc_ref(v___y_2499_);
                lean_inc(v___y_2498_);
                lean_inc_ref(v___y_2497_);
                lean_inc(v___y_2496_);
                lean_inc_ref(v___y_2495_);
                lean_inc(v___y_2494_);
                lean_inc_ref(v___y_2493_);
                v___x_2504_ = lean_apply_11(
                    v_a_2491_,
                    v___y_2493_,
                    v___y_2494_,
                    v___y_2495_,
                    v___y_2496_,
                    v___y_2497_,
                    v___y_2498_,
                    v___y_2499_,
                    v___y_2500_,
                    v___y_2501_,
                    v___y_2502_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2504_) == 0 {
                    v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
                    lean_inc(v_a_2505_);
                    if lean_obj_tag(v_a_2505_) == 0 {
                        v_done_2506_ = lean_ctor_get_uint8(v_a_2505_, 0 as u32);
                        if v_done_2506_ == 0 {
                            lean_dec_ref_known(v___x_2504_, 1);
                            v_contextDependent_2507_ = lean_ctor_get_uint8(v_a_2505_, 1 as u32);
                            lean_dec_ref_known(v_a_2505_, 0);
                            v___x_2508_ = lean_apply_11(
                                v_a_2492_,
                                v___y_2493_,
                                v___y_2494_,
                                v___y_2495_,
                                v___y_2496_,
                                v___y_2497_,
                                v___y_2498_,
                                v___y_2499_,
                                v___y_2500_,
                                v___y_2501_,
                                v___y_2502_,
                                lean_box(0),
                            );
                            if lean_obj_tag(v___x_2508_) == 0 {
                                v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
                                lean_inc(v_a_2509_);
                                if v_contextDependent_2507_ == 0 {
                                    lean_dec(v_a_2509_);
                                    return v___x_2508_;
                                } else {
                                    if lean_obj_tag(v_a_2509_) == 0 {
                                        v_contextDependent_2521_ =
                                            lean_ctor_get_uint8(v_a_2509_, 1 as u32);
                                        v___y_2511_ = v_contextDependent_2521_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_contextDependent_2522_ = lean_ctor_get_uint8(
                                            v_a_2509_,
                                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1)
                                                as u32,
                                        );
                                        v___y_2511_ = v_contextDependent_2522_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                return v___x_2508_;
                            }
                        } else {
                            lean_dec_ref_known(v_a_2505_, 0);
                            lean_dec(v___y_2502_);
                            lean_dec_ref(v___y_2501_);
                            lean_dec(v___y_2500_);
                            lean_dec_ref(v___y_2499_);
                            lean_dec(v___y_2498_);
                            lean_dec_ref(v___y_2497_);
                            lean_dec(v___y_2496_);
                            lean_dec_ref(v___y_2495_);
                            lean_dec(v___y_2494_);
                            lean_dec_ref(v___y_2493_);
                            lean_dec_ref(v_a_2492_);
                            return v___x_2504_;
                        }
                    } else {
                        lean_dec_ref_known(v_a_2505_, 2);
                        lean_dec(v___y_2502_);
                        lean_dec_ref(v___y_2501_);
                        lean_dec(v___y_2500_);
                        lean_dec_ref(v___y_2499_);
                        lean_dec(v___y_2498_);
                        lean_dec_ref(v___y_2497_);
                        lean_dec(v___y_2496_);
                        lean_dec_ref(v___y_2495_);
                        lean_dec(v___y_2494_);
                        lean_dec_ref(v___y_2493_);
                        lean_dec_ref(v_a_2492_);
                        return v___x_2504_;
                    }
                } else {
                    lean_dec(v___y_2502_);
                    lean_dec_ref(v___y_2501_);
                    lean_dec(v___y_2500_);
                    lean_dec_ref(v___y_2499_);
                    lean_dec(v___y_2498_);
                    lean_dec_ref(v___y_2497_);
                    lean_dec(v___y_2496_);
                    lean_dec_ref(v___y_2495_);
                    lean_dec(v___y_2494_);
                    lean_dec_ref(v___y_2493_);
                    lean_dec_ref(v_a_2492_);
                    return v___x_2504_;
                }
            }
            1 => {
                if v___y_2511_ == 0 {
                    v_isSharedCheck_2519_ = (!lean_is_exclusive(v___x_2508_)) as u8;
                    if v_isSharedCheck_2519_ == 0 {
                        v_unused_2520_ = lean_ctor_get(v___x_2508_, 0);
                        lean_dec(v_unused_2520_);
                        v___x_2513_ = v___x_2508_;
                        v_isShared_2514_ = v_isSharedCheck_2519_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2508_);
                        v___x_2513_ = lean_box(0);
                        v_isShared_2514_ = v_isSharedCheck_2519_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2509_);
                    return v___x_2508_;
                }
            }
            2 => {
                v___x_2515_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2509_);
                if v_isShared_2514_ == 0 {
                    lean_ctor_set(v___x_2513_, 0, v___x_2515_);
                    v___x_2517_ = v___x_2513_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
                    v___x_2517_ = v_reuseFailAlloc_2518_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2517_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___lam__0___boxed(
    mut v_a_2523_: *mut LeanObject,
    mut v_a_2524_: *mut LeanObject,
    mut v___y_2525_: *mut LeanObject,
    mut v___y_2526_: *mut LeanObject,
    mut v___y_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
    mut v___y_2530_: *mut LeanObject,
    mut v___y_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
    mut v___y_2535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2536_: *mut LeanObject = core::ptr::null_mut();
    v_res_2536_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___lam__0(v_a_2523_, v_a_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
    return v_res_2536_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse(
    mut v_stx_2544_: *mut LeanObject,
    mut v_a_2545_: *mut LeanObject,
    mut v_a_2546_: *mut LeanObject,
    mut v_a_2547_: *mut LeanObject,
    mut v_a_2548_: *mut LeanObject,
    mut v_a_2549_: *mut LeanObject,
    mut v_a_2550_: *mut LeanObject,
    mut v_a_2551_: *mut LeanObject,
    mut v_a_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: u8 = 0;
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v___f_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2554_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1;
                lean_inc(v_stx_2544_);
                v___x_2555_ = l_Lean_Syntax_isOfKind(v_stx_2544_, v___x_2554_);
                if v___x_2555_ == 0 {
                    lean_dec(v_stx_2544_);
                    v___x_2556_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                    return v___x_2556_;
                } else {
                    v___x_2557_ = lean_unsigned_to_nat(0);
                    v___x_2558_ = l_Lean_Syntax_getArg(v_stx_2544_, v___x_2557_);
                    v___x_2559_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(
                        v___x_2558_,
                        v_a_2545_,
                        v_a_2546_,
                        v_a_2547_,
                        v_a_2548_,
                        v_a_2549_,
                        v_a_2550_,
                        v_a_2551_,
                        v_a_2552_,
                    );
                    if lean_obj_tag(v___x_2559_) == 0 {
                        v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
                        lean_inc(v_a_2560_);
                        lean_dec_ref_known(v___x_2559_, 1);
                        v___x_2561_ = lean_unsigned_to_nat(2);
                        v___x_2562_ = l_Lean_Syntax_getArg(v_stx_2544_, v___x_2561_);
                        lean_dec(v_stx_2544_);
                        v___x_2563_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(
                            v___x_2562_,
                            v_a_2545_,
                            v_a_2546_,
                            v_a_2547_,
                            v_a_2548_,
                            v_a_2549_,
                            v_a_2550_,
                            v_a_2551_,
                            v_a_2552_,
                        );
                        if lean_obj_tag(v___x_2563_) == 0 {
                            v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
                            v_isSharedCheck_2572_ = (!lean_is_exclusive(v___x_2563_)) as u8;
                            if v_isSharedCheck_2572_ == 0 {
                                v___x_2566_ = v___x_2563_;
                                v_isShared_2567_ = v_isSharedCheck_2572_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2564_);
                                lean_dec(v___x_2563_);
                                v___x_2566_ = lean_box(0);
                                v_isShared_2567_ = v_isSharedCheck_2572_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2560_);
                            return v___x_2563_;
                        }
                    } else {
                        lean_dec(v_stx_2544_);
                        return v___x_2559_;
                    }
                }
            }
            1 => {
                v___f_2568_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                lean_closure_set(v___f_2568_, 0, v_a_2560_);
                lean_closure_set(v___f_2568_, 1, v_a_2564_);
                if v_isShared_2567_ == 0 {
                    lean_ctor_set(v___x_2566_, 0, v___f_2568_);
                    v___x_2570_ = v___x_2566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___f_2568_);
                    v___x_2570_ = v_reuseFailAlloc_2571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___boxed(
    mut v_stx_2573_: *mut LeanObject,
    mut v_a_2574_: *mut LeanObject,
    mut v_a_2575_: *mut LeanObject,
    mut v_a_2576_: *mut LeanObject,
    mut v_a_2577_: *mut LeanObject,
    mut v_a_2578_: *mut LeanObject,
    mut v_a_2579_: *mut LeanObject,
    mut v_a_2580_: *mut LeanObject,
    mut v_a_2581_: *mut LeanObject,
    mut v_a_2582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2583_: *mut LeanObject = core::ptr::null_mut();
    v_res_2583_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse(v_stx_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
    lean_dec(v_a_2581_);
    lean_dec_ref(v_a_2580_);
    lean_dec(v_a_2579_);
    lean_dec_ref(v_a_2578_);
    lean_dec(v_a_2577_);
    lean_dec_ref(v_a_2576_);
    lean_dec(v_a_2575_);
    lean_dec_ref(v_a_2574_);
    return v_res_2583_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1()
-> *mut LeanObject {
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    v___x_2589_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_2590_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1;
    v___x_2591_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__1;
    v___x_2592_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2593_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2589_,
        v___x_2590_,
        v___x_2591_,
        v___x_2592_,
    );
    return v___x_2593_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___boxed(
    mut v_a_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2595_: *mut LeanObject = core::ptr::null_mut();
    v_res_2595_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1();
    return v_res_2595_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen(
    mut v_stx_2603_: *mut LeanObject,
    mut v_a_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
    mut v_a_2607_: *mut LeanObject,
    mut v_a_2608_: *mut LeanObject,
    mut v_a_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    v___x_2613_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1;
    lean_inc(v_stx_2603_);
    v___x_2614_ = l_Lean_Syntax_isOfKind(v_stx_2603_, v___x_2613_);
    if v___x_2614_ == 0 {
        let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_2603_);
        v___x_2615_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
        return v___x_2615_;
    } else {
        let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
        v___x_2616_ = lean_unsigned_to_nat(1);
        v___x_2617_ = l_Lean_Syntax_getArg(v_stx_2603_, v___x_2616_);
        lean_dec(v_stx_2603_);
        v___x_2618_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(
            v___x_2617_,
            v_a_2604_,
            v_a_2605_,
            v_a_2606_,
            v_a_2607_,
            v_a_2608_,
            v_a_2609_,
            v_a_2610_,
            v_a_2611_,
        );
        return v___x_2618_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___boxed(
    mut v_stx_2619_: *mut LeanObject,
    mut v_a_2620_: *mut LeanObject,
    mut v_a_2621_: *mut LeanObject,
    mut v_a_2622_: *mut LeanObject,
    mut v_a_2623_: *mut LeanObject,
    mut v_a_2624_: *mut LeanObject,
    mut v_a_2625_: *mut LeanObject,
    mut v_a_2626_: *mut LeanObject,
    mut v_a_2627_: *mut LeanObject,
    mut v_a_2628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2629_: *mut LeanObject = core::ptr::null_mut();
    v_res_2629_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen(v_stx_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
    lean_dec(v_a_2627_);
    lean_dec_ref(v_a_2626_);
    lean_dec(v_a_2625_);
    lean_dec_ref(v_a_2624_);
    lean_dec(v_a_2623_);
    lean_dec_ref(v_a_2622_);
    lean_dec(v_a_2621_);
    lean_dec_ref(v_a_2620_);
    return v_res_2629_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1()
-> *mut LeanObject {
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    v___x_2635_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_2636_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1;
    v___x_2637_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__1;
    v___x_2638_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2639_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2635_,
        v___x_2636_,
        v___x_2637_,
        v___x_2638_,
    );
    return v___x_2639_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___boxed(
    mut v_a_2640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2641_: *mut LeanObject = core::ptr::null_mut();
    v_res_2641_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1();
    return v_res_2641_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg()
-> *mut LeanObject {
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    v___x_2644_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg___closed__0;
    v___x_2645_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2645_, 0, v___x_2644_);
    return v___x_2645_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg___boxed(
    mut v_a_2646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2647_: *mut LeanObject = core::ptr::null_mut();
    v_res_2647_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg();
    return v_res_2647_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf(
    mut v_x_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
    mut v_a_2651_: *mut LeanObject,
    mut v_a_2652_: *mut LeanObject,
    mut v_a_2653_: *mut LeanObject,
    mut v_a_2654_: *mut LeanObject,
    mut v_a_2655_: *mut LeanObject,
    mut v_a_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    v___x_2658_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg();
    return v___x_2658_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___boxed(
    mut v_x_2659_: *mut LeanObject,
    mut v_a_2660_: *mut LeanObject,
    mut v_a_2661_: *mut LeanObject,
    mut v_a_2662_: *mut LeanObject,
    mut v_a_2663_: *mut LeanObject,
    mut v_a_2664_: *mut LeanObject,
    mut v_a_2665_: *mut LeanObject,
    mut v_a_2666_: *mut LeanObject,
    mut v_a_2667_: *mut LeanObject,
    mut v_a_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2669_: *mut LeanObject = core::ptr::null_mut();
    v_res_2669_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf(v_x_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
    lean_dec(v_a_2667_);
    lean_dec_ref(v_a_2666_);
    lean_dec(v_a_2665_);
    lean_dec_ref(v_a_2664_);
    lean_dec(v_a_2663_);
    lean_dec_ref(v_a_2662_);
    lean_dec(v_a_2661_);
    lean_dec_ref(v_a_2660_);
    lean_dec(v_x_2659_);
    return v_res_2669_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1()
-> *mut LeanObject {
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    v___x_2682_ = l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute;
    v___x_2683_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1;
    v___x_2684_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__3;
    v___x_2685_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2686_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2682_,
        v___x_2683_,
        v___x_2684_,
        v___x_2685_,
    );
    return v___x_2686_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___boxed(
    mut v_a_2687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2688_: *mut LeanObject = core::ptr::null_mut();
    v_res_2688_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1();
    return v_res_2688_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___redArg()
-> *mut LeanObject {
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    v___x_2690_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0;
    v___x_2691_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2691_, 0, v___x_2690_);
    return v___x_2691_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___redArg___boxed(
    mut v_a_2692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2693_: *mut LeanObject = core::ptr::null_mut();
    v_res_2693_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___redArg();
    return v_res_2693_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone(
    mut v_x_2694_: *mut LeanObject,
    mut v_a_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
    mut v_a_2699_: *mut LeanObject,
    mut v_a_2700_: *mut LeanObject,
    mut v_a_2701_: *mut LeanObject,
    mut v_a_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    v___x_2704_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___redArg();
    return v___x_2704_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___boxed(
    mut v_x_2705_: *mut LeanObject,
    mut v_a_2706_: *mut LeanObject,
    mut v_a_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
    mut v_a_2709_: *mut LeanObject,
    mut v_a_2710_: *mut LeanObject,
    mut v_a_2711_: *mut LeanObject,
    mut v_a_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2715_: *mut LeanObject = core::ptr::null_mut();
    v_res_2715_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone(v_x_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
    lean_dec(v_a_2713_);
    lean_dec_ref(v_a_2712_);
    lean_dec(v_a_2711_);
    lean_dec_ref(v_a_2710_);
    lean_dec(v_a_2709_);
    lean_dec_ref(v_a_2708_);
    lean_dec(v_a_2707_);
    lean_dec_ref(v_a_2706_);
    lean_dec(v_x_2705_);
    return v_res_2715_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1()
-> *mut LeanObject {
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    v___x_2728_ = l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute;
    v___x_2729_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1;
    v___x_2730_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__3;
    v___x_2731_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2732_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2728_,
        v___x_2729_,
        v___x_2730_,
        v___x_2731_,
    );
    return v___x_2732_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___boxed(
    mut v_a_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2734_: *mut LeanObject = core::ptr::null_mut();
    v_res_2734_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1();
    return v_res_2734_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen(
    mut v_stx_2742_: *mut LeanObject,
    mut v_a_2743_: *mut LeanObject,
    mut v_a_2744_: *mut LeanObject,
    mut v_a_2745_: *mut LeanObject,
    mut v_a_2746_: *mut LeanObject,
    mut v_a_2747_: *mut LeanObject,
    mut v_a_2748_: *mut LeanObject,
    mut v_a_2749_: *mut LeanObject,
    mut v_a_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: u8 = 0;
    v___x_2752_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1;
    lean_inc(v_stx_2742_);
    v___x_2753_ = l_Lean_Syntax_isOfKind(v_stx_2742_, v___x_2752_);
    if v___x_2753_ == 0 {
        let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_2742_);
        v___x_2754_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
        return v___x_2754_;
    } else {
        let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
        v___x_2755_ = lean_unsigned_to_nat(1);
        v___x_2756_ = l_Lean_Syntax_getArg(v_stx_2742_, v___x_2755_);
        lean_dec(v_stx_2742_);
        v___x_2757_ = l_Lean_Elab_Tactic_Grind_elabSymDischarger(
            v___x_2756_,
            v_a_2743_,
            v_a_2744_,
            v_a_2745_,
            v_a_2746_,
            v_a_2747_,
            v_a_2748_,
            v_a_2749_,
            v_a_2750_,
        );
        return v___x_2757_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___boxed(
    mut v_stx_2758_: *mut LeanObject,
    mut v_a_2759_: *mut LeanObject,
    mut v_a_2760_: *mut LeanObject,
    mut v_a_2761_: *mut LeanObject,
    mut v_a_2762_: *mut LeanObject,
    mut v_a_2763_: *mut LeanObject,
    mut v_a_2764_: *mut LeanObject,
    mut v_a_2765_: *mut LeanObject,
    mut v_a_2766_: *mut LeanObject,
    mut v_a_2767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2768_: *mut LeanObject = core::ptr::null_mut();
    v_res_2768_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen(v_stx_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
    lean_dec(v_a_2766_);
    lean_dec_ref(v_a_2765_);
    lean_dec(v_a_2764_);
    lean_dec_ref(v_a_2763_);
    lean_dec(v_a_2762_);
    lean_dec_ref(v_a_2761_);
    lean_dec(v_a_2760_);
    lean_dec_ref(v_a_2759_);
    return v_res_2768_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1()
-> *mut LeanObject {
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    v___x_2774_ = l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute;
    v___x_2775_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1;
    v___x_2776_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__1;
    v___x_2777_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2778_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2774_,
        v___x_2775_,
        v___x_2776_,
        v___x_2777_,
    );
    return v___x_2778_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___boxed(
    mut v_a_2779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2780_: *mut LeanObject = core::ptr::null_mut();
    v_res_2780_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1();
    return v_res_2780_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Sym_Simp_SimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Sym_Simp_SimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(builtin);
}

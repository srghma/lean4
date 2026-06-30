// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.SimprocDSLBuiltin
// Imports: Lean.Elab.Tactic.Grind.SimprocDSL Init.Sym.Simp.SimprocDSL Lean.Meta.Sym.Simp.EvalGround Lean.Meta.Sym.Simp.Telescope Lean.Meta.Sym.Simp.ControlFlow Lean.Meta.Sym.Simp.Forall Lean.Meta.Sym.Simp.Rewrite
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Prelude::{
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
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg___closed__0_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_evalGround___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 1, m_objs: [((( 255 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__4_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 114, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__4_value) as *mut leanh::LeanObject,15642365844547147657 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__6_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__9_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__9_value) as *mut leanh::LeanObject,5444244426488757208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__11_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__11_value) as *mut leanh::LeanObject,5409699204079762053 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__13_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__12_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__13_value) as *mut leanh::LeanObject,4907018543776028915 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__15_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 105, 109, 112, 114, 111, 99, 68, 83, 76, 66, 117, 105, 108, 116, 105, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__14_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__15_value) as *mut leanh::LeanObject,16249163007935939648 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__16_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,5385254338892450297 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__17_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,4693334292471861852 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__18_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__9_value) as *mut leanh::LeanObject,3389843619649221974 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__19_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__11_value) as *mut leanh::LeanObject,14478700687058776363 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__20_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__13_value) as *mut leanh::LeanObject,16293275684050261757 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__22_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 71, 114, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__22_value) as *mut leanh::LeanObject,14723896219049396130 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_simpTelescope___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 108, 101, 115, 99, 111, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__0_value) as *mut leanh::LeanObject,4998230570037354350 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__2_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 84, 101, 108, 101, 115, 99, 111, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__2_value) as *mut leanh::LeanObject,6770449457282690577 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_simpControl___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 110, 116, 114, 111, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__0_value) as *mut leanh::LeanObject,5081612414781455787 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__2_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 67, 111, 110, 116, 114, 111, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__2_value) as *mut leanh::LeanObject,6182495194412741250 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_simp___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__1_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 114, 114, 111, 119, 84, 101, 108, 101, 115, 99, 111, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__0_value) as *mut leanh::LeanObject,7377854587226246167 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__2_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 65, 114, 114, 111, 119, 84, 101, 108, 101, 115, 99, 111, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__2_value) as *mut leanh::LeanObject,11648593786210260458 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 101, 108, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__0_value) as *mut leanh::LeanObject,3624192759600632721 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__2_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 83, 101, 108, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__2_value) as *mut leanh::LeanObject,10598441156433296818 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__0_value) as *mut leanh::LeanObject,5819120222105569584 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__2_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 78, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__2_value) as *mut leanh::LeanObject,13045445119418784023 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_dischargeNone___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 119, 114, 105, 116, 101, 83, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__0_value) as *mut leanh::LeanObject,10120069549607349517 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__2_value: leanh::LeanStringObject<31> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 83, 121, 109, 46, 115, 105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 32, 115, 101, 116, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__6_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 82, 101, 119, 114, 105, 116, 101, 83, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__0_value) as *mut leanh::LeanObject,16264364062687217872 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 119, 114, 105, 116, 101, 73, 110, 108, 105, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__2_value) as *mut leanh::LeanObject,5467082909805454615 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__4_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 82, 101, 119, 114, 105, 116, 101, 73, 110, 108, 105, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__0_value) as *mut leanh::LeanObject,17295928722472936712 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 84, 104, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__0_value) as *mut leanh::LeanObject,564218847374344423 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 65, 110, 100, 84, 104, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__0_value) as *mut leanh::LeanObject,10140887910739941129 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 114, 69, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__0_value) as *mut leanh::LeanObject,11113107058493755383 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 79, 114, 69, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__0_value) as *mut leanh::LeanObject,11181433736188212634 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 105, 109, 112, 114, 111, 99, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__0_value) as *mut leanh::LeanObject,15836888127685990580 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__0_value) as *mut leanh::LeanObject,13499288908001983991 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 115, 99, 104, 83, 101, 108, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__0_value) as *mut leanh::LeanObject,16169981844629337600 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 108, 97, 98, 68, 105, 115, 99, 104, 83, 101, 108, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__2_value) as *mut leanh::LeanObject,5948902922022391747 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 115, 99, 104, 78, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__0_value) as *mut leanh::LeanObject,12137791703934599550 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 108, 97, 98, 68, 105, 115, 99, 104, 78, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__2_value) as *mut leanh::LeanObject,6880829856682481277 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 105, 115, 99, 104, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__2_value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__3_value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__0_value) as *mut leanh::LeanObject,381305762770861206 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 68, 105, 115, 99, 104, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__21_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__0_value) as *mut leanh::LeanObject,14580698448265653145 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg___closed__0;
    v___x_1395_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1395_, 0, v___x_1394_);
    return v___x_1395_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg___boxed(
    mut v_a_1396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1397_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg();
    return v_res_1397_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround(
    mut v_x_1398_: *mut leanh::LeanObject,
    mut v_a_1399_: *mut leanh::LeanObject,
    mut v_a_1400_: *mut leanh::LeanObject,
    mut v_a_1401_: *mut leanh::LeanObject,
    mut v_a_1402_: *mut leanh::LeanObject,
    mut v_a_1403_: *mut leanh::LeanObject,
    mut v_a_1404_: *mut leanh::LeanObject,
    mut v_a_1405_: *mut leanh::LeanObject,
    mut v_a_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___redArg();
    return v___x_1408_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___boxed(
    mut v_x_1409_: *mut leanh::LeanObject,
    mut v_a_1410_: *mut leanh::LeanObject,
    mut v_a_1411_: *mut leanh::LeanObject,
    mut v_a_1412_: *mut leanh::LeanObject,
    mut v_a_1413_: *mut leanh::LeanObject,
    mut v_a_1414_: *mut leanh::LeanObject,
    mut v_a_1415_: *mut leanh::LeanObject,
    mut v_a_1416_: *mut leanh::LeanObject,
    mut v_a_1417_: *mut leanh::LeanObject,
    mut v_a_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1419_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround(v_x_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_);
    leanh::lean_dec(v_a_1417_);
    leanh::lean_dec_ref(v_a_1416_);
    leanh::lean_dec(v_a_1415_);
    leanh::lean_dec_ref(v_a_1414_);
    leanh::lean_dec(v_a_1413_);
    leanh::lean_dec_ref(v_a_1412_);
    leanh::lean_dec(v_a_1411_);
    leanh::lean_dec_ref(v_a_1410_);
    leanh::lean_dec(v_x_1409_);
    return v_res_1419_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1()
-> *mut leanh::LeanObject {
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1475_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__5;
    v___x_1476_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___closed__23;
    v___x_1477_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1478_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1474_,
        v___x_1475_,
        v___x_1476_,
        v___x_1477_,
    );
    return v___x_1478_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1___boxed(
    mut v_a_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1480_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1();
    return v_res_1480_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg___closed__0;
    v___x_1484_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1484_, 0, v___x_1483_);
    return v___x_1484_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg___boxed(
    mut v_a_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1486_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg();
    return v_res_1486_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope(
    mut v_x_1487_: *mut leanh::LeanObject,
    mut v_a_1488_: *mut leanh::LeanObject,
    mut v_a_1489_: *mut leanh::LeanObject,
    mut v_a_1490_: *mut leanh::LeanObject,
    mut v_a_1491_: *mut leanh::LeanObject,
    mut v_a_1492_: *mut leanh::LeanObject,
    mut v_a_1493_: *mut leanh::LeanObject,
    mut v_a_1494_: *mut leanh::LeanObject,
    mut v_a_1495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___redArg();
    return v___x_1497_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___boxed(
    mut v_x_1498_: *mut leanh::LeanObject,
    mut v_a_1499_: *mut leanh::LeanObject,
    mut v_a_1500_: *mut leanh::LeanObject,
    mut v_a_1501_: *mut leanh::LeanObject,
    mut v_a_1502_: *mut leanh::LeanObject,
    mut v_a_1503_: *mut leanh::LeanObject,
    mut v_a_1504_: *mut leanh::LeanObject,
    mut v_a_1505_: *mut leanh::LeanObject,
    mut v_a_1506_: *mut leanh::LeanObject,
    mut v_a_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope(v_x_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
    leanh::lean_dec(v_a_1506_);
    leanh::lean_dec_ref(v_a_1505_);
    leanh::lean_dec(v_a_1504_);
    leanh::lean_dec_ref(v_a_1503_);
    leanh::lean_dec(v_a_1502_);
    leanh::lean_dec_ref(v_a_1501_);
    leanh::lean_dec(v_a_1500_);
    leanh::lean_dec_ref(v_a_1499_);
    leanh::lean_dec(v_x_1498_);
    return v_res_1508_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1()
-> *mut leanh::LeanObject {
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1521_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1522_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__1;
    v___x_1523_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___closed__3;
    v___x_1524_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1525_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1521_,
        v___x_1522_,
        v___x_1523_,
        v___x_1524_,
    );
    return v___x_1525_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1___boxed(
    mut v_a_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1527_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1();
    return v_res_1527_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg___closed__0;
    v___x_1531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
    return v___x_1531_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg___boxed(
    mut v_a_1532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1533_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg();
    return v_res_1533_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl(
    mut v_x_1534_: *mut leanh::LeanObject,
    mut v_a_1535_: *mut leanh::LeanObject,
    mut v_a_1536_: *mut leanh::LeanObject,
    mut v_a_1537_: *mut leanh::LeanObject,
    mut v_a_1538_: *mut leanh::LeanObject,
    mut v_a_1539_: *mut leanh::LeanObject,
    mut v_a_1540_: *mut leanh::LeanObject,
    mut v_a_1541_: *mut leanh::LeanObject,
    mut v_a_1542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1544_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___redArg();
    return v___x_1544_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___boxed(
    mut v_x_1545_: *mut leanh::LeanObject,
    mut v_a_1546_: *mut leanh::LeanObject,
    mut v_a_1547_: *mut leanh::LeanObject,
    mut v_a_1548_: *mut leanh::LeanObject,
    mut v_a_1549_: *mut leanh::LeanObject,
    mut v_a_1550_: *mut leanh::LeanObject,
    mut v_a_1551_: *mut leanh::LeanObject,
    mut v_a_1552_: *mut leanh::LeanObject,
    mut v_a_1553_: *mut leanh::LeanObject,
    mut v_a_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1555_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl(v_x_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
    leanh::lean_dec(v_a_1553_);
    leanh::lean_dec_ref(v_a_1552_);
    leanh::lean_dec(v_a_1551_);
    leanh::lean_dec_ref(v_a_1550_);
    leanh::lean_dec(v_a_1549_);
    leanh::lean_dec_ref(v_a_1548_);
    leanh::lean_dec(v_a_1547_);
    leanh::lean_dec_ref(v_a_1546_);
    leanh::lean_dec(v_x_1545_);
    return v_res_1555_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1()
-> *mut leanh::LeanObject {
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1568_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1569_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__1;
    v___x_1570_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___closed__3;
    v___x_1571_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1572_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1568_,
        v___x_1569_,
        v___x_1570_,
        v___x_1571_,
    );
    return v___x_1572_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1___boxed(
    mut v_a_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1();
    return v_res_1574_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1579_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__1;
    v___x_1580_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1580_, 0, v___x_1579_);
    return v___x_1580_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___boxed(
    mut v_a_1581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1582_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg();
    return v_res_1582_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope(
    mut v_x_1583_: *mut leanh::LeanObject,
    mut v_a_1584_: *mut leanh::LeanObject,
    mut v_a_1585_: *mut leanh::LeanObject,
    mut v_a_1586_: *mut leanh::LeanObject,
    mut v_a_1587_: *mut leanh::LeanObject,
    mut v_a_1588_: *mut leanh::LeanObject,
    mut v_a_1589_: *mut leanh::LeanObject,
    mut v_a_1590_: *mut leanh::LeanObject,
    mut v_a_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1593_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg();
    return v___x_1593_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___boxed(
    mut v_x_1594_: *mut leanh::LeanObject,
    mut v_a_1595_: *mut leanh::LeanObject,
    mut v_a_1596_: *mut leanh::LeanObject,
    mut v_a_1597_: *mut leanh::LeanObject,
    mut v_a_1598_: *mut leanh::LeanObject,
    mut v_a_1599_: *mut leanh::LeanObject,
    mut v_a_1600_: *mut leanh::LeanObject,
    mut v_a_1601_: *mut leanh::LeanObject,
    mut v_a_1602_: *mut leanh::LeanObject,
    mut v_a_1603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope(v_x_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
    leanh::lean_dec(v_a_1602_);
    leanh::lean_dec_ref(v_a_1601_);
    leanh::lean_dec(v_a_1600_);
    leanh::lean_dec_ref(v_a_1599_);
    leanh::lean_dec(v_a_1598_);
    leanh::lean_dec_ref(v_a_1597_);
    leanh::lean_dec(v_a_1596_);
    leanh::lean_dec_ref(v_a_1595_);
    leanh::lean_dec(v_x_1594_);
    return v_res_1604_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1()
-> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1618_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__1;
    v___x_1619_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___closed__3;
    v___x_1620_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1621_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1617_,
        v___x_1618_,
        v___x_1619_,
        v___x_1620_,
    );
    return v___x_1621_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1___boxed(
    mut v_a_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1623_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1();
    return v_res_1623_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___redArg___closed__0;
    v___x_1626_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1626_, 0, v___x_1625_);
    return v___x_1626_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___redArg___boxed(
    mut v_a_1627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1628_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___redArg();
    return v_res_1628_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf(
    mut v_x_1629_: *mut leanh::LeanObject,
    mut v_a_1630_: *mut leanh::LeanObject,
    mut v_a_1631_: *mut leanh::LeanObject,
    mut v_a_1632_: *mut leanh::LeanObject,
    mut v_a_1633_: *mut leanh::LeanObject,
    mut v_a_1634_: *mut leanh::LeanObject,
    mut v_a_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1639_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___redArg();
    return v___x_1639_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___boxed(
    mut v_x_1640_: *mut leanh::LeanObject,
    mut v_a_1641_: *mut leanh::LeanObject,
    mut v_a_1642_: *mut leanh::LeanObject,
    mut v_a_1643_: *mut leanh::LeanObject,
    mut v_a_1644_: *mut leanh::LeanObject,
    mut v_a_1645_: *mut leanh::LeanObject,
    mut v_a_1646_: *mut leanh::LeanObject,
    mut v_a_1647_: *mut leanh::LeanObject,
    mut v_a_1648_: *mut leanh::LeanObject,
    mut v_a_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1650_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf(v_x_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
    leanh::lean_dec(v_a_1648_);
    leanh::lean_dec_ref(v_a_1647_);
    leanh::lean_dec(v_a_1646_);
    leanh::lean_dec_ref(v_a_1645_);
    leanh::lean_dec(v_a_1644_);
    leanh::lean_dec_ref(v_a_1643_);
    leanh::lean_dec(v_a_1642_);
    leanh::lean_dec_ref(v_a_1641_);
    leanh::lean_dec(v_x_1640_);
    return v_res_1650_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1()
-> *mut leanh::LeanObject {
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1664_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__1;
    v___x_1665_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___closed__3;
    v___x_1666_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1667_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1663_,
        v___x_1664_,
        v___x_1665_,
        v___x_1666_,
    );
    return v___x_1667_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1___boxed(
    mut v_a_1668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1669_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1();
    return v_res_1669_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0(
    mut v_x_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
    mut v___y_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
    mut v___y_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___closed__0;
    v___x_1684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1684_, 0, v___x_1683_);
    return v___x_1684_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0___boxed(
    mut v_x_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
    mut v___y_1687_: *mut leanh::LeanObject,
    mut v___y_1688_: *mut leanh::LeanObject,
    mut v___y_1689_: *mut leanh::LeanObject,
    mut v___y_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
    mut v___y_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
    mut v___y_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1696_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___lam__0(v_x_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
    leanh::lean_dec(v___y_1694_);
    leanh::lean_dec_ref(v___y_1693_);
    leanh::lean_dec(v___y_1692_);
    leanh::lean_dec_ref(v___y_1691_);
    leanh::lean_dec(v___y_1690_);
    leanh::lean_dec_ref(v___y_1689_);
    leanh::lean_dec(v___y_1688_);
    leanh::lean_dec_ref(v___y_1687_);
    leanh::lean_dec(v___y_1686_);
    leanh::lean_dec_ref(v_x_1685_);
    return v_res_1696_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg()
-> *mut leanh::LeanObject {
    let mut v___f_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1699_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___closed__0;
    v___x_1700_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1700_, 0, v___f_1699_);
    return v___x_1700_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg___boxed(
    mut v_a_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg();
    return v_res_1702_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone(
    mut v_x_1703_: *mut leanh::LeanObject,
    mut v_a_1704_: *mut leanh::LeanObject,
    mut v_a_1705_: *mut leanh::LeanObject,
    mut v_a_1706_: *mut leanh::LeanObject,
    mut v_a_1707_: *mut leanh::LeanObject,
    mut v_a_1708_: *mut leanh::LeanObject,
    mut v_a_1709_: *mut leanh::LeanObject,
    mut v_a_1710_: *mut leanh::LeanObject,
    mut v_a_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1713_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___redArg();
    return v___x_1713_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___boxed(
    mut v_x_1714_: *mut leanh::LeanObject,
    mut v_a_1715_: *mut leanh::LeanObject,
    mut v_a_1716_: *mut leanh::LeanObject,
    mut v_a_1717_: *mut leanh::LeanObject,
    mut v_a_1718_: *mut leanh::LeanObject,
    mut v_a_1719_: *mut leanh::LeanObject,
    mut v_a_1720_: *mut leanh::LeanObject,
    mut v_a_1721_: *mut leanh::LeanObject,
    mut v_a_1722_: *mut leanh::LeanObject,
    mut v_a_1723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1724_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone(v_x_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_);
    leanh::lean_dec(v_a_1722_);
    leanh::lean_dec_ref(v_a_1721_);
    leanh::lean_dec(v_a_1720_);
    leanh::lean_dec_ref(v_a_1719_);
    leanh::lean_dec(v_a_1718_);
    leanh::lean_dec_ref(v_a_1717_);
    leanh::lean_dec(v_a_1716_);
    leanh::lean_dec_ref(v_a_1715_);
    leanh::lean_dec(v_x_1714_);
    return v_res_1724_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1()
-> *mut leanh::LeanObject {
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1737_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_1738_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__1;
    v___x_1739_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___closed__3;
    v___x_1740_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1741_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1737_,
        v___x_1738_,
        v___x_1739_,
        v___x_1740_,
    );
    return v___x_1741_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1___boxed(
    mut v_a_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1743_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1();
    return v_res_1743_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger(
    mut v_discharger_x3f_1745_: *mut leanh::LeanObject,
    mut v_a_1746_: *mut leanh::LeanObject,
    mut v_a_1747_: *mut leanh::LeanObject,
    mut v_a_1748_: *mut leanh::LeanObject,
    mut v_a_1749_: *mut leanh::LeanObject,
    mut v_a_1750_: *mut leanh::LeanObject,
    mut v_a_1751_: *mut leanh::LeanObject,
    mut v_a_1752_: *mut leanh::LeanObject,
    mut v_a_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_discharger_x3f_1745_) == 1 {
        let mut v_val_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1755_ = leanh::lean_ctor_get(v_discharger_x3f_1745_, 0);
        leanh::lean_inc(v_val_1755_);
        leanh::lean_dec_ref_known(v_discharger_x3f_1745_, 1);
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
        let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_discharger_x3f_1745_);
        v___x_1757_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0;
        v___x_1758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1758_, 0, v___x_1757_);
        return v___x_1758_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___boxed(
    mut v_discharger_x3f_1759_: *mut leanh::LeanObject,
    mut v_a_1760_: *mut leanh::LeanObject,
    mut v_a_1761_: *mut leanh::LeanObject,
    mut v_a_1762_: *mut leanh::LeanObject,
    mut v_a_1763_: *mut leanh::LeanObject,
    mut v_a_1764_: *mut leanh::LeanObject,
    mut v_a_1765_: *mut leanh::LeanObject,
    mut v_a_1766_: *mut leanh::LeanObject,
    mut v_a_1767_: *mut leanh::LeanObject,
    mut v_a_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1769_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger(v_discharger_x3f_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
    leanh::lean_dec(v_a_1767_);
    leanh::lean_dec_ref(v_a_1766_);
    leanh::lean_dec(v_a_1765_);
    leanh::lean_dec_ref(v_a_1764_);
    leanh::lean_dec(v_a_1763_);
    leanh::lean_dec_ref(v_a_1762_);
    leanh::lean_dec(v_a_1761_);
    leanh::lean_dec_ref(v_a_1760_);
    return v_res_1769_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = leanh::lean_box(0);
    v___x_1771_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1772_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
    leanh::lean_ctor_set(v___x_1772_, 1, v___x_1770_);
    return v___x_1772_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___closed__0);
    v___x_1775_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1775_, 0, v___x_1774_);
    return v___x_1775_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg___boxed(
    mut v___y_1776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
    return v_res_1777_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0(
    mut v_00_u03b1_1778_: *mut leanh::LeanObject,
    mut v___y_1779_: *mut leanh::LeanObject,
    mut v___y_1780_: *mut leanh::LeanObject,
    mut v___y_1781_: *mut leanh::LeanObject,
    mut v___y_1782_: *mut leanh::LeanObject,
    mut v___y_1783_: *mut leanh::LeanObject,
    mut v___y_1784_: *mut leanh::LeanObject,
    mut v___y_1785_: *mut leanh::LeanObject,
    mut v___y_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1788_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
    return v___x_1788_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___boxed(
    mut v_00_u03b1_1789_: *mut leanh::LeanObject,
    mut v___y_1790_: *mut leanh::LeanObject,
    mut v___y_1791_: *mut leanh::LeanObject,
    mut v___y_1792_: *mut leanh::LeanObject,
    mut v___y_1793_: *mut leanh::LeanObject,
    mut v___y_1794_: *mut leanh::LeanObject,
    mut v___y_1795_: *mut leanh::LeanObject,
    mut v___y_1796_: *mut leanh::LeanObject,
    mut v___y_1797_: *mut leanh::LeanObject,
    mut v___y_1798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1799_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0(v_00_u03b1_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
    leanh::lean_dec(v___y_1797_);
    leanh::lean_dec_ref(v___y_1796_);
    leanh::lean_dec(v___y_1795_);
    leanh::lean_dec_ref(v___y_1794_);
    leanh::lean_dec(v___y_1793_);
    leanh::lean_dec_ref(v___y_1792_);
    leanh::lean_dec(v___y_1791_);
    leanh::lean_dec_ref(v___y_1790_);
    return v_res_1799_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1_spec__2(
    mut v_msgData_1800_: *mut leanh::LeanObject,
    mut v___y_1801_: *mut leanh::LeanObject,
    mut v___y_1802_: *mut leanh::LeanObject,
    mut v___y_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1806_ = lean_st_ref_get(v___y_1804_);
    v_env_1807_ = leanh::lean_ctor_get(v___x_1806_, 0);
    leanh::lean_inc_ref(v_env_1807_);
    leanh::lean_dec(v___x_1806_);
    v___x_1808_ = lean_st_ref_get(v___y_1802_);
    v_mctx_1809_ = leanh::lean_ctor_get(v___x_1808_, 0);
    leanh::lean_inc_ref(v_mctx_1809_);
    leanh::lean_dec(v___x_1808_);
    v_lctx_1810_ = leanh::lean_ctor_get(v___y_1801_, 2);
    v_options_1811_ = leanh::lean_ctor_get(v___y_1803_, 2);
    leanh::lean_inc_ref(v_options_1811_);
    leanh::lean_inc_ref(v_lctx_1810_);
    v___x_1812_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1812_, 0, v_env_1807_);
    leanh::lean_ctor_set(v___x_1812_, 1, v_mctx_1809_);
    leanh::lean_ctor_set(v___x_1812_, 2, v_lctx_1810_);
    leanh::lean_ctor_set(v___x_1812_, 3, v_options_1811_);
    v___x_1813_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    leanh::lean_ctor_set(v___x_1813_, 1, v_msgData_1800_);
    v___x_1814_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1814_, 0, v___x_1813_);
    return v___x_1814_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
    mut v___y_1818_: *mut leanh::LeanObject,
    mut v___y_1819_: *mut leanh::LeanObject,
    mut v___y_1820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1821_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1_spec__2(v_msgData_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
    leanh::lean_dec(v___y_1819_);
    leanh::lean_dec_ref(v___y_1818_);
    leanh::lean_dec(v___y_1817_);
    leanh::lean_dec_ref(v___y_1816_);
    return v_res_1821_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___redArg(
    mut v_msg_1822_: *mut leanh::LeanObject,
    mut v___y_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
    mut v___y_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1828_ = leanh::lean_ctor_get(v___y_1825_, 5);
                v___x_1829_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1_spec__2(v_msg_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
                v_a_1830_ = leanh::lean_ctor_get(v___x_1829_, 0);
                v_isSharedCheck_1838_ = (!leanh::lean_is_exclusive(v___x_1829_)) as u8;
                if v_isSharedCheck_1838_ == 0 {
                    v___x_1832_ = v___x_1829_;
                    v_isShared_1833_ = v_isSharedCheck_1838_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1830_);
                    leanh::lean_dec(v___x_1829_);
                    v___x_1832_ = leanh::lean_box(0);
                    v_isShared_1833_ = v_isSharedCheck_1838_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1828_);
                v___x_1834_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1834_, 0, v_ref_1828_);
                leanh::lean_ctor_set(v___x_1834_, 1, v_a_1830_);
                if v_isShared_1833_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1832_, 1);
                    leanh::lean_ctor_set(v___x_1832_, 0, v___x_1834_);
                    v___x_1836_ = v___x_1832_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
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
    mut v_msg_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
    mut v___y_1843_: *mut leanh::LeanObject,
    mut v___y_1844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1845_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___redArg(v_msg_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
    leanh::lean_dec(v___y_1843_);
    leanh::lean_dec_ref(v___y_1842_);
    leanh::lean_dec(v___y_1841_);
    leanh::lean_dec_ref(v___y_1840_);
    return v_res_1845_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___redArg(
    mut v_ref_1846_: *mut leanh::LeanObject,
    mut v_msg_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
    mut v___y_1849_: *mut leanh::LeanObject,
    mut v___y_1850_: *mut leanh::LeanObject,
    mut v___y_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
    mut v___y_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1869_: u8 = 0;
    let mut v_cancelTk_x3f_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1871_: u8 = 0;
    let mut v_inheritedTraceOptions_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1857_ = leanh::lean_ctor_get(v___y_1854_, 0);
    v_fileMap_1858_ = leanh::lean_ctor_get(v___y_1854_, 1);
    v_options_1859_ = leanh::lean_ctor_get(v___y_1854_, 2);
    v_currRecDepth_1860_ = leanh::lean_ctor_get(v___y_1854_, 3);
    v_maxRecDepth_1861_ = leanh::lean_ctor_get(v___y_1854_, 4);
    v_ref_1862_ = leanh::lean_ctor_get(v___y_1854_, 5);
    v_currNamespace_1863_ = leanh::lean_ctor_get(v___y_1854_, 6);
    v_openDecls_1864_ = leanh::lean_ctor_get(v___y_1854_, 7);
    v_initHeartbeats_1865_ = leanh::lean_ctor_get(v___y_1854_, 8);
    v_maxHeartbeats_1866_ = leanh::lean_ctor_get(v___y_1854_, 9);
    v_quotContext_1867_ = leanh::lean_ctor_get(v___y_1854_, 10);
    v_currMacroScope_1868_ = leanh::lean_ctor_get(v___y_1854_, 11);
    v_diag_1869_ = leanh::lean_ctor_get_uint8(
        v___y_1854_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1870_ = leanh::lean_ctor_get(v___y_1854_, 12);
    v_suppressElabErrors_1871_ = leanh::lean_ctor_get_uint8(
        v___y_1854_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1872_ = leanh::lean_ctor_get(v___y_1854_, 13);
    v_ref_1873_ = l_Lean_replaceRef(v_ref_1846_, v_ref_1862_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1872_);
    leanh::lean_inc(v_cancelTk_x3f_1870_);
    leanh::lean_inc(v_currMacroScope_1868_);
    leanh::lean_inc(v_quotContext_1867_);
    leanh::lean_inc(v_maxHeartbeats_1866_);
    leanh::lean_inc(v_initHeartbeats_1865_);
    leanh::lean_inc(v_openDecls_1864_);
    leanh::lean_inc(v_currNamespace_1863_);
    leanh::lean_inc(v_maxRecDepth_1861_);
    leanh::lean_inc(v_currRecDepth_1860_);
    leanh::lean_inc_ref(v_options_1859_);
    leanh::lean_inc_ref(v_fileMap_1858_);
    leanh::lean_inc_ref(v_fileName_1857_);
    v___x_1874_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1874_, 0, v_fileName_1857_);
    leanh::lean_ctor_set(v___x_1874_, 1, v_fileMap_1858_);
    leanh::lean_ctor_set(v___x_1874_, 2, v_options_1859_);
    leanh::lean_ctor_set(v___x_1874_, 3, v_currRecDepth_1860_);
    leanh::lean_ctor_set(v___x_1874_, 4, v_maxRecDepth_1861_);
    leanh::lean_ctor_set(v___x_1874_, 5, v_ref_1873_);
    leanh::lean_ctor_set(v___x_1874_, 6, v_currNamespace_1863_);
    leanh::lean_ctor_set(v___x_1874_, 7, v_openDecls_1864_);
    leanh::lean_ctor_set(v___x_1874_, 8, v_initHeartbeats_1865_);
    leanh::lean_ctor_set(v___x_1874_, 9, v_maxHeartbeats_1866_);
    leanh::lean_ctor_set(v___x_1874_, 10, v_quotContext_1867_);
    leanh::lean_ctor_set(v___x_1874_, 11, v_currMacroScope_1868_);
    leanh::lean_ctor_set(v___x_1874_, 12, v_cancelTk_x3f_1870_);
    leanh::lean_ctor_set(v___x_1874_, 13, v_inheritedTraceOptions_1872_);
    leanh::lean_ctor_set_uint8(
        v___x_1874_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1869_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1874_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1871_,
    );
    v___x_1875_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___redArg(v_msg_1847_, v___y_1852_, v___y_1853_, v___x_1874_, v___y_1855_);
    leanh::lean_dec_ref_known(v___x_1874_, 14);
    return v___x_1875_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___redArg___boxed(
    mut v_ref_1876_: *mut leanh::LeanObject,
    mut v_msg_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
    mut v___y_1879_: *mut leanh::LeanObject,
    mut v___y_1880_: *mut leanh::LeanObject,
    mut v___y_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1887_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___redArg(v_ref_1876_, v_msg_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
    leanh::lean_dec(v___y_1885_);
    leanh::lean_dec_ref(v___y_1884_);
    leanh::lean_dec(v___y_1883_);
    leanh::lean_dec_ref(v___y_1882_);
    leanh::lean_dec(v___y_1881_);
    leanh::lean_dec_ref(v___y_1880_);
    leanh::lean_dec(v___y_1879_);
    leanh::lean_dec_ref(v___y_1878_);
    leanh::lean_dec(v_ref_1876_);
    return v_res_1887_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1896_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__2;
    v___x_1897_ = l_Lean_stringToMessageData(v___x_1896_);
    return v___x_1897_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__4;
    v___x_1900_ = l_Lean_stringToMessageData(v___x_1899_);
    return v___x_1900_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet(
    mut v_stx_1904_: *mut leanh::LeanObject,
    mut v_a_1905_: *mut leanh::LeanObject,
    mut v_a_1906_: *mut leanh::LeanObject,
    mut v_a_1907_: *mut leanh::LeanObject,
    mut v_a_1908_: *mut leanh::LeanObject,
    mut v_a_1909_: *mut leanh::LeanObject,
    mut v_a_1910_: *mut leanh::LeanObject,
    mut v_a_1911_: *mut leanh::LeanObject,
    mut v_a_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_setName_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1939_: u8 = 0;
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut v_a_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v_a_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1956_: u8 = 0;
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1970_: u8 = 0;
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: u8 = 0;
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1914_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1;
                leanh::lean_inc(v_stx_1904_);
                v___x_1915_ = l_Lean_Syntax_isOfKind(v_stx_1904_, v___x_1914_);
                if v___x_1915_ == 0 {
                    leanh::lean_dec(v_stx_1904_);
                    v___x_1916_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                    return v___x_1916_;
                } else {
                    v___x_1917_ = leanh::lean_unsigned_to_nat(1);
                    v_setName_1918_ = l_Lean_Syntax_getArg(v_stx_1904_, v___x_1917_);
                    v___x_1975_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__7;
                    leanh::lean_inc(v_setName_1918_);
                    v___x_1976_ = l_Lean_Syntax_isOfKind(v_setName_1918_, v___x_1975_);
                    if v___x_1976_ == 0 {
                        leanh::lean_dec(v_setName_1918_);
                        leanh::lean_dec(v_stx_1904_);
                        v___x_1977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                        return v___x_1977_;
                    } else {
                        v___x_1978_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1979_ = l_Lean_Syntax_getArg(v_stx_1904_, v___x_1978_);
                        leanh::lean_dec(v_stx_1904_);
                        v___x_1980_ = l_Lean_Syntax_isNone(v___x_1979_);
                        if v___x_1980_ == 0 {
                            leanh::lean_inc(v___x_1979_);
                            v___x_1981_ = l_Lean_Syntax_matchesNull(v___x_1979_, v___x_1978_);
                            if v___x_1981_ == 0 {
                                leanh::lean_dec(v___x_1979_);
                                leanh::lean_dec(v_setName_1918_);
                                v___x_1982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                                return v___x_1982_;
                            } else {
                                v_d_x3f_1983_ = l_Lean_Syntax_getArg(v___x_1979_, v___x_1917_);
                                leanh::lean_dec(v___x_1979_);
                                v___x_1984_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1984_, 0, v_d_x3f_1983_);
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
                            leanh::lean_dec(v___x_1979_);
                            v___x_1985_ = leanh::lean_box(0);
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
                leanh::lean_dec(v___x_1929_);
                if leanh::lean_obj_tag(v___x_1930_) == 0 {
                    v_a_1931_ = leanh::lean_ctor_get(v___x_1930_, 0);
                    leanh::lean_inc(v_a_1931_);
                    leanh::lean_dec_ref_known(v___x_1930_, 1);
                    if leanh::lean_obj_tag(v_a_1931_) == 1 {
                        leanh::lean_dec(v_setName_1918_);
                        v_val_1932_ = leanh::lean_ctor_get(v_a_1931_, 0);
                        leanh::lean_inc(v_val_1932_);
                        leanh::lean_dec_ref_known(v_a_1931_, 1);
                        v___x_1933_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(
                            v_val_1932_,
                            v___y_1928_,
                        );
                        leanh::lean_dec(v_val_1932_);
                        if leanh::lean_obj_tag(v___x_1933_) == 0 {
                            v_a_1934_ = leanh::lean_ctor_get(v___x_1933_, 0);
                            leanh::lean_inc(v_a_1934_);
                            leanh::lean_dec_ref_known(v___x_1933_, 1);
                            v___x_1935_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger(v_d_x3f_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
                            if leanh::lean_obj_tag(v___x_1935_) == 0 {
                                v_a_1936_ = leanh::lean_ctor_get(v___x_1935_, 0);
                                v_isSharedCheck_1944_ =
                                    (!leanh::lean_is_exclusive(v___x_1935_)) as u8;
                                if v_isSharedCheck_1944_ == 0 {
                                    v___x_1938_ = v___x_1935_;
                                    v_isShared_1939_ = v_isSharedCheck_1944_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1936_);
                                    leanh::lean_dec(v___x_1935_);
                                    v___x_1938_ = leanh::lean_box(0);
                                    v_isShared_1939_ = v_isSharedCheck_1944_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_1934_);
                                v_a_1945_ = leanh::lean_ctor_get(v___x_1935_, 0);
                                v_isSharedCheck_1952_ =
                                    (!leanh::lean_is_exclusive(v___x_1935_)) as u8;
                                if v_isSharedCheck_1952_ == 0 {
                                    v___x_1947_ = v___x_1935_;
                                    v_isShared_1948_ = v_isSharedCheck_1952_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1945_);
                                    leanh::lean_dec(v___x_1935_);
                                    v___x_1947_ = leanh::lean_box(0);
                                    v_isShared_1948_ = v_isSharedCheck_1952_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_d_x3f_1920_);
                            v_a_1953_ = leanh::lean_ctor_get(v___x_1933_, 0);
                            v_isSharedCheck_1960_ =
                                (!leanh::lean_is_exclusive(v___x_1933_)) as u8;
                            if v_isSharedCheck_1960_ == 0 {
                                v___x_1955_ = v___x_1933_;
                                v_isShared_1956_ = v_isSharedCheck_1960_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1953_);
                                leanh::lean_dec(v___x_1933_);
                                v___x_1955_ = leanh::lean_box(0);
                                v_isShared_1956_ = v_isSharedCheck_1960_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1931_);
                        leanh::lean_dec(v_d_x3f_1920_);
                        v___x_1961_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3_once), _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__3);
                        leanh::lean_inc(v_setName_1918_);
                        v___x_1962_ = l_Lean_MessageData_ofSyntax(v_setName_1918_);
                        v___x_1963_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1963_, 0, v___x_1961_);
                        leanh::lean_ctor_set(v___x_1963_, 1, v___x_1962_);
                        v___x_1964_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5_once), _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__5);
                        v___x_1965_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1965_, 0, v___x_1963_);
                        leanh::lean_ctor_set(v___x_1965_, 1, v___x_1964_);
                        v___x_1966_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___redArg(v_setName_1918_, v___x_1965_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
                        leanh::lean_dec(v_setName_1918_);
                        return v___x_1966_;
                    }
                } else {
                    leanh::lean_dec(v_d_x3f_1920_);
                    leanh::lean_dec(v_setName_1918_);
                    v_a_1967_ = leanh::lean_ctor_get(v___x_1930_, 0);
                    v_isSharedCheck_1974_ = (!leanh::lean_is_exclusive(v___x_1930_)) as u8;
                    if v_isSharedCheck_1974_ == 0 {
                        v___x_1969_ = v___x_1930_;
                        v_isShared_1970_ = v_isSharedCheck_1974_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1967_);
                        leanh::lean_dec(v___x_1930_);
                        v___x_1969_ = leanh::lean_box(0);
                        v_isShared_1970_ = v_isSharedCheck_1974_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1940_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed as *mut core::ffi::c_void,
                    13,
                    2,
                );
                leanh::lean_closure_set(v___x_1940_, 0, v_a_1934_);
                leanh::lean_closure_set(v___x_1940_, 1, v_a_1936_);
                if v_isShared_1939_ == 0 {
                    leanh::lean_ctor_set(v___x_1938_, 0, v___x_1940_);
                    v___x_1942_ = v___x_1938_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1943_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
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
                    v_reuseFailAlloc_1951_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
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
                    v_reuseFailAlloc_1959_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
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
                    v_reuseFailAlloc_1973_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
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
    mut v_stx_1986_: *mut leanh::LeanObject,
    mut v_a_1987_: *mut leanh::LeanObject,
    mut v_a_1988_: *mut leanh::LeanObject,
    mut v_a_1989_: *mut leanh::LeanObject,
    mut v_a_1990_: *mut leanh::LeanObject,
    mut v_a_1991_: *mut leanh::LeanObject,
    mut v_a_1992_: *mut leanh::LeanObject,
    mut v_a_1993_: *mut leanh::LeanObject,
    mut v_a_1994_: *mut leanh::LeanObject,
    mut v_a_1995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1996_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet(v_stx_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
    leanh::lean_dec(v_a_1994_);
    leanh::lean_dec_ref(v_a_1993_);
    leanh::lean_dec(v_a_1992_);
    leanh::lean_dec_ref(v_a_1991_);
    leanh::lean_dec(v_a_1990_);
    leanh::lean_dec_ref(v_a_1989_);
    leanh::lean_dec(v_a_1988_);
    leanh::lean_dec_ref(v_a_1987_);
    return v_res_1996_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1(
    mut v_00_u03b1_1997_: *mut leanh::LeanObject,
    mut v_ref_1998_: *mut leanh::LeanObject,
    mut v_msg_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
    mut v___y_2006_: *mut leanh::LeanObject,
    mut v___y_2007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2009_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___redArg(v_ref_1998_, v_msg_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
    return v___x_2009_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1___boxed(
    mut v_00_u03b1_2010_: *mut leanh::LeanObject,
    mut v_ref_2011_: *mut leanh::LeanObject,
    mut v_msg_2012_: *mut leanh::LeanObject,
    mut v___y_2013_: *mut leanh::LeanObject,
    mut v___y_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
    mut v___y_2018_: *mut leanh::LeanObject,
    mut v___y_2019_: *mut leanh::LeanObject,
    mut v___y_2020_: *mut leanh::LeanObject,
    mut v___y_2021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2022_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1(v_00_u03b1_2010_, v_ref_2011_, v_msg_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
    leanh::lean_dec(v___y_2020_);
    leanh::lean_dec_ref(v___y_2019_);
    leanh::lean_dec(v___y_2018_);
    leanh::lean_dec_ref(v___y_2017_);
    leanh::lean_dec(v___y_2016_);
    leanh::lean_dec_ref(v___y_2015_);
    leanh::lean_dec(v___y_2014_);
    leanh::lean_dec_ref(v___y_2013_);
    leanh::lean_dec(v_ref_2011_);
    return v_res_2022_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1(
    mut v_00_u03b1_2023_: *mut leanh::LeanObject,
    mut v_msg_2024_: *mut leanh::LeanObject,
    mut v___y_2025_: *mut leanh::LeanObject,
    mut v___y_2026_: *mut leanh::LeanObject,
    mut v___y_2027_: *mut leanh::LeanObject,
    mut v___y_2028_: *mut leanh::LeanObject,
    mut v___y_2029_: *mut leanh::LeanObject,
    mut v___y_2030_: *mut leanh::LeanObject,
    mut v___y_2031_: *mut leanh::LeanObject,
    mut v___y_2032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___redArg(v_msg_2024_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
    return v___x_2034_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1___boxed(
    mut v_00_u03b1_2035_: *mut leanh::LeanObject,
    mut v_msg_2036_: *mut leanh::LeanObject,
    mut v___y_2037_: *mut leanh::LeanObject,
    mut v___y_2038_: *mut leanh::LeanObject,
    mut v___y_2039_: *mut leanh::LeanObject,
    mut v___y_2040_: *mut leanh::LeanObject,
    mut v___y_2041_: *mut leanh::LeanObject,
    mut v___y_2042_: *mut leanh::LeanObject,
    mut v___y_2043_: *mut leanh::LeanObject,
    mut v___y_2044_: *mut leanh::LeanObject,
    mut v___y_2045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2046_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__1_spec__1(v_00_u03b1_2035_, v_msg_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
    leanh::lean_dec(v___y_2044_);
    leanh::lean_dec_ref(v___y_2043_);
    leanh::lean_dec(v___y_2042_);
    leanh::lean_dec_ref(v___y_2041_);
    leanh::lean_dec(v___y_2040_);
    leanh::lean_dec_ref(v___y_2039_);
    leanh::lean_dec(v___y_2038_);
    leanh::lean_dec_ref(v___y_2037_);
    return v_res_2046_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1()
-> *mut leanh::LeanObject {
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2052_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_2053_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__1;
    v___x_2054_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___closed__1;
    v___x_2055_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2056_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2052_,
        v___x_2053_,
        v___x_2054_,
        v___x_2055_,
    );
    return v___x_2056_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1___boxed(
    mut v_a_2057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2058_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1();
    return v_res_2058_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___redArg(
    mut v_as_2059_: *mut leanh::LeanObject,
    mut v_sz_2060_: usize,
    mut v_i_2061_: usize,
    mut v_b_2062_: *mut leanh::LeanObject,
    mut v___y_2063_: *mut leanh::LeanObject,
    mut v___y_2064_: *mut leanh::LeanObject,
    mut v___y_2065_: *mut leanh::LeanObject,
    mut v___y_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: usize = 0;
    let mut v___x_2077_: usize = 0;
    let mut v_a_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2082_: u8 = 0;
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2086_: u8 = 0;
    let mut v_a_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2068_ = lean_usize_dec_lt(v_i_2061_, v_sz_2060_);
                if v___x_2068_ == 0 {
                    v___x_2069_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2069_, 0, v_b_2062_);
                    return v___x_2069_;
                } else {
                    v_a_2070_ = lean_array_uget_borrowed(v_as_2059_, v_i_2061_);
                    leanh::lean_inc(v_a_2070_);
                    v___x_2071_ =
                        l_Lean_realizeGlobalConstNoOverload(v_a_2070_, v___y_2065_, v___y_2066_);
                    if leanh::lean_obj_tag(v___x_2071_) == 0 {
                        v_a_2072_ = leanh::lean_ctor_get(v___x_2071_, 0);
                        leanh::lean_inc(v_a_2072_);
                        leanh::lean_dec_ref_known(v___x_2071_, 1);
                        v___x_2073_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(
                            v_a_2072_,
                            v___y_2063_,
                            v___y_2064_,
                            v___y_2065_,
                            v___y_2066_,
                        );
                        if leanh::lean_obj_tag(v___x_2073_) == 0 {
                            v_a_2074_ = leanh::lean_ctor_get(v___x_2073_, 0);
                            leanh::lean_inc(v_a_2074_);
                            leanh::lean_dec_ref_known(v___x_2073_, 1);
                            v___x_2075_ =
                                l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_2062_, v_a_2074_);
                            v___x_2076_ = 1usize;
                            v___x_2077_ = lean_usize_add(v_i_2061_, v___x_2076_);
                            v_i_2061_ = v___x_2077_;
                            v_b_2062_ = v___x_2075_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_2062_);
                            v_a_2079_ = leanh::lean_ctor_get(v___x_2073_, 0);
                            v_isSharedCheck_2086_ =
                                (!leanh::lean_is_exclusive(v___x_2073_)) as u8;
                            if v_isSharedCheck_2086_ == 0 {
                                v___x_2081_ = v___x_2073_;
                                v_isShared_2082_ = v_isSharedCheck_2086_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2079_);
                                leanh::lean_dec(v___x_2073_);
                                v___x_2081_ = leanh::lean_box(0);
                                v_isShared_2082_ = v_isSharedCheck_2086_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_2062_);
                        v_a_2087_ = leanh::lean_ctor_get(v___x_2071_, 0);
                        v_isSharedCheck_2094_ =
                            (!leanh::lean_is_exclusive(v___x_2071_)) as u8;
                        if v_isSharedCheck_2094_ == 0 {
                            v___x_2089_ = v___x_2071_;
                            v_isShared_2090_ = v_isSharedCheck_2094_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2087_);
                            leanh::lean_dec(v___x_2071_);
                            v___x_2089_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2085_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
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
                    v_reuseFailAlloc_2093_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
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
    mut v_as_2095_: *mut leanh::LeanObject,
    mut v_sz_2096_: *mut leanh::LeanObject,
    mut v_i_2097_: *mut leanh::LeanObject,
    mut v_b_2098_: *mut leanh::LeanObject,
    mut v___y_2099_: *mut leanh::LeanObject,
    mut v___y_2100_: *mut leanh::LeanObject,
    mut v___y_2101_: *mut leanh::LeanObject,
    mut v___y_2102_: *mut leanh::LeanObject,
    mut v___y_2103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2104_: usize = 0;
    let mut v_i_boxed_2105_: usize = 0;
    let mut v_res_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2104_ = leanh::lean_unbox_usize(v_sz_2096_);
    leanh::lean_dec(v_sz_2096_);
    v_i_boxed_2105_ = leanh::lean_unbox_usize(v_i_2097_);
    leanh::lean_dec(v_i_2097_);
    v_res_2106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___redArg(v_as_2095_, v_sz_boxed_2104_, v_i_boxed_2105_, v_b_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
    leanh::lean_dec(v___y_2102_);
    leanh::lean_dec_ref(v___y_2101_);
    leanh::lean_dec(v___y_2100_);
    leanh::lean_dec_ref(v___y_2099_);
    leanh::lean_dec_ref(v_as_2095_);
    return v_res_2106_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__2(
    mut v___x_2107_: u8,
    mut v_as_2108_: *mut leanh::LeanObject,
    mut v_i_2109_: usize,
    mut v_stop_2110_: usize,
    mut v_b_2111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: usize = 0;
    let mut v___x_2115_: usize = 0;
    let mut v___x_2117_: u8 = 0;
    let mut v_fst_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: u8 = 0;
    let mut v_snd_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2128_: u8 = 0;
    let mut v_unused_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut v_unused_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2117_ = lean_usize_dec_eq(v_i_2109_, v_stop_2110_);
                if v___x_2117_ == 0 {
                    v_fst_2118_ = leanh::lean_ctor_get(v_b_2111_, 0);
                    v___x_2119_ = (leanh::lean_unbox(v_fst_2118_) as u8);
                    if v___x_2119_ == 0 {
                        v_snd_2120_ = leanh::lean_ctor_get(v_b_2111_, 1);
                        v_isSharedCheck_2128_ = (!leanh::lean_is_exclusive(v_b_2111_)) as u8;
                        if v_isSharedCheck_2128_ == 0 {
                            v_unused_2129_ = leanh::lean_ctor_get(v_b_2111_, 0);
                            leanh::lean_dec(v_unused_2129_);
                            v___x_2122_ = v_b_2111_;
                            v_isShared_2123_ = v_isSharedCheck_2128_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_2120_);
                            leanh::lean_dec(v_b_2111_);
                            v___x_2122_ = leanh::lean_box(0);
                            v_isShared_2123_ = v_isSharedCheck_2128_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_2130_ = leanh::lean_ctor_get(v_b_2111_, 1);
                        v_isSharedCheck_2140_ = (!leanh::lean_is_exclusive(v_b_2111_)) as u8;
                        if v_isSharedCheck_2140_ == 0 {
                            v_unused_2141_ = leanh::lean_ctor_get(v_b_2111_, 0);
                            leanh::lean_dec(v_unused_2141_);
                            v___x_2132_ = v_b_2111_;
                            v_isShared_2133_ = v_isSharedCheck_2140_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_2130_);
                            leanh::lean_dec(v_b_2111_);
                            v___x_2132_ = leanh::lean_box(0);
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
                v___x_2124_ = leanh::lean_box((v___x_2107_) as usize);
                if v_isShared_2123_ == 0 {
                    leanh::lean_ctor_set(v___x_2122_, 0, v___x_2124_);
                    v___x_2126_ = v___x_2122_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_snd_2120_);
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
                leanh::lean_inc(v___x_2134_);
                v___x_2135_ = lean_array_push(v_snd_2130_, v___x_2134_);
                v___x_2136_ = leanh::lean_box((v___x_2117_) as usize);
                if v_isShared_2133_ == 0 {
                    leanh::lean_ctor_set(v___x_2132_, 1, v___x_2135_);
                    leanh::lean_ctor_set(v___x_2132_, 0, v___x_2136_);
                    v___x_2138_ = v___x_2132_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2139_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2135_);
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
    mut v___x_2142_: *mut leanh::LeanObject,
    mut v_as_2143_: *mut leanh::LeanObject,
    mut v_i_2144_: *mut leanh::LeanObject,
    mut v_stop_2145_: *mut leanh::LeanObject,
    mut v_b_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2743__boxed_2147_: u8 = 0;
    let mut v_i_boxed_2148_: usize = 0;
    let mut v_stop_boxed_2149_: usize = 0;
    let mut v_res_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2743__boxed_2147_ = (leanh::lean_unbox(v___x_2142_) as u8);
    v_i_boxed_2148_ = leanh::lean_unbox_usize(v_i_2144_);
    leanh::lean_dec(v_i_2144_);
    v_stop_boxed_2149_ = leanh::lean_unbox_usize(v_stop_2145_);
    leanh::lean_dec(v_stop_2145_);
    v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__2(v___x_2743__boxed_2147_, v_as_2143_, v_i_boxed_2148_, v_stop_boxed_2149_, v_b_2146_);
    leanh::lean_dec_ref(v_as_2143_);
    return v_res_2150_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__0(
    mut v_sz_2151_: usize,
    mut v_i_2152_: usize,
    mut v_bs_2153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: usize = 0;
    let mut v___x_2163_: usize = 0;
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2154_ = lean_usize_dec_lt(v_i_2152_, v_sz_2151_);
                if v___x_2154_ == 0 {
                    v___x_2155_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2155_, 0, v_bs_2153_);
                    return v___x_2155_;
                } else {
                    v_v_2156_ = lean_array_uget(v_bs_2153_, v_i_2152_);
                    v___x_2157_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___closed__7;
                    leanh::lean_inc(v_v_2156_);
                    v___x_2158_ = l_Lean_Syntax_isOfKind(v_v_2156_, v___x_2157_);
                    if v___x_2158_ == 0 {
                        leanh::lean_dec(v_v_2156_);
                        leanh::lean_dec_ref(v_bs_2153_);
                        v___x_2159_ = leanh::lean_box(0);
                        return v___x_2159_;
                    } else {
                        v___x_2160_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_2166_: *mut leanh::LeanObject,
    mut v_i_2167_: *mut leanh::LeanObject,
    mut v_bs_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2169_: usize = 0;
    let mut v_i_boxed_2170_: usize = 0;
    let mut v_res_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2169_ = leanh::lean_unbox_usize(v_sz_2166_);
    leanh::lean_dec(v_sz_2166_);
    v_i_boxed_2170_ = leanh::lean_unbox_usize(v_i_2167_);
    leanh::lean_dec(v_i_2167_);
    v_res_2171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__0(v_sz_boxed_2169_, v_i_boxed_2170_, v_bs_2168_);
    return v_res_2171_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2172_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_thms_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2173_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0_once), _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__0);
    v_thms_2174_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v_thms_2174_, 0, v___x_2173_);
    return v_thms_2174_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline(
    mut v_stx_2184_: *mut leanh::LeanObject,
    mut v_a_2185_: *mut leanh::LeanObject,
    mut v_a_2186_: *mut leanh::LeanObject,
    mut v_a_2187_: *mut leanh::LeanObject,
    mut v_a_2188_: *mut leanh::LeanObject,
    mut v_a_2189_: *mut leanh::LeanObject,
    mut v_a_2190_: *mut leanh::LeanObject,
    mut v_a_2191_: *mut leanh::LeanObject,
    mut v_a_2192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2195_: usize = 0;
    let mut v___y_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_thms_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2207_: usize = 0;
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2214_: u8 = 0;
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2219_: u8 = 0;
    let mut v_a_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2227_: u8 = 0;
    let mut v_a_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2243_: usize = 0;
    let mut v___x_2244_: usize = 0;
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u8 = 0;
    let mut v___x_2254_: u8 = 0;
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: u8 = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2271_: usize = 0;
    let mut v___x_2272_: usize = 0;
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: usize = 0;
    let mut v___x_2276_: usize = 0;
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2236_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3;
                leanh::lean_inc(v_stx_2184_);
                v___x_2237_ = l_Lean_Syntax_isOfKind(v_stx_2184_, v___x_2236_);
                if v___x_2237_ == 0 {
                    leanh::lean_dec(v_stx_2184_);
                    v___x_2238_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                    return v___x_2238_;
                } else {
                    v___x_2239_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2240_ = leanh::lean_unsigned_to_nat(2);
                    v___x_2262_ = l_Lean_Syntax_getArg(v_stx_2184_, v___x_2240_);
                    v___x_2263_ = l_Lean_Syntax_getArgs(v___x_2262_);
                    leanh::lean_dec(v___x_2262_);
                    v___x_2264_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2265_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__4;
                    v___x_2266_ = lean_array_get_size(v___x_2263_);
                    v___x_2267_ = lean_nat_dec_lt(v___x_2264_, v___x_2266_);
                    if v___x_2267_ == 0 {
                        leanh::lean_dec_ref(v___x_2263_);
                        v___y_2242_ = v___x_2265_;
                        state = 8;
                        continue;
                    } else {
                        v___x_2268_ = leanh::lean_box((v___x_2237_) as usize);
                        v___x_2269_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2269_, 0, v___x_2268_);
                        leanh::lean_ctor_set(v___x_2269_, 1, v___x_2265_);
                        v___x_2270_ = lean_nat_dec_le(v___x_2266_, v___x_2266_);
                        if v___x_2270_ == 0 {
                            if v___x_2267_ == 0 {
                                leanh::lean_dec_ref_known(v___x_2269_, 2);
                                leanh::lean_dec_ref(v___x_2263_);
                                v___y_2242_ = v___x_2265_;
                                state = 8;
                                continue;
                            } else {
                                v___x_2271_ = 0usize;
                                v___x_2272_ = lean_usize_of_nat(v___x_2266_);
                                v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__2(v___x_2237_, v___x_2263_, v___x_2271_, v___x_2272_, v___x_2269_);
                                leanh::lean_dec_ref(v___x_2263_);
                                v_snd_2274_ = leanh::lean_ctor_get(v___x_2273_, 1);
                                leanh::lean_inc(v_snd_2274_);
                                leanh::lean_dec_ref(v___x_2273_);
                                v___y_2242_ = v_snd_2274_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___x_2275_ = 0usize;
                            v___x_2276_ = lean_usize_of_nat(v___x_2266_);
                            v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__2(v___x_2237_, v___x_2263_, v___x_2275_, v___x_2276_, v___x_2269_);
                            leanh::lean_dec_ref(v___x_2263_);
                            v_snd_2278_ = leanh::lean_ctor_get(v___x_2277_, 1);
                            leanh::lean_inc(v_snd_2278_);
                            leanh::lean_dec_ref(v___x_2277_);
                            v___y_2242_ = v_snd_2278_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_thms_2206_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1_once), _init_l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__1);
                v_sz_2207_ = lean_array_size(v___y_2196_);
                v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___redArg(v___y_2196_, v_sz_2207_, v___y_2195_, v_thms_2206_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
                leanh::lean_dec_ref(v___y_2196_);
                if leanh::lean_obj_tag(v___x_2208_) == 0 {
                    v_a_2209_ = leanh::lean_ctor_get(v___x_2208_, 0);
                    leanh::lean_inc(v_a_2209_);
                    leanh::lean_dec_ref_known(v___x_2208_, 1);
                    v___x_2210_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger(v_d_x3f_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
                    if leanh::lean_obj_tag(v___x_2210_) == 0 {
                        v_a_2211_ = leanh::lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2219_ =
                            (!leanh::lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2219_ == 0 {
                            v___x_2213_ = v___x_2210_;
                            v_isShared_2214_ = v_isSharedCheck_2219_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2211_);
                            leanh::lean_dec(v___x_2210_);
                            v___x_2213_ = leanh::lean_box(0);
                            v_isShared_2214_ = v_isSharedCheck_2219_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2209_);
                        v_a_2220_ = leanh::lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2227_ =
                            (!leanh::lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2227_ == 0 {
                            v___x_2222_ = v___x_2210_;
                            v_isShared_2223_ = v_isSharedCheck_2227_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2220_);
                            leanh::lean_dec(v___x_2210_);
                            v___x_2222_ = leanh::lean_box(0);
                            v_isShared_2223_ = v_isSharedCheck_2227_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_d_x3f_2197_);
                    v_a_2228_ = leanh::lean_ctor_get(v___x_2208_, 0);
                    v_isSharedCheck_2235_ = (!leanh::lean_is_exclusive(v___x_2208_)) as u8;
                    if v_isSharedCheck_2235_ == 0 {
                        v___x_2230_ = v___x_2208_;
                        v_isShared_2231_ = v_isSharedCheck_2235_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2228_);
                        leanh::lean_dec(v___x_2208_);
                        v___x_2230_ = leanh::lean_box(0);
                        v_isShared_2231_ = v_isSharedCheck_2235_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2215_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed as *mut core::ffi::c_void,
                    13,
                    2,
                );
                leanh::lean_closure_set(v___x_2215_, 0, v_a_2209_);
                leanh::lean_closure_set(v___x_2215_, 1, v_a_2211_);
                if v_isShared_2214_ == 0 {
                    leanh::lean_ctor_set(v___x_2213_, 0, v___x_2215_);
                    v___x_2217_ = v___x_2213_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2218_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
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
                    v_reuseFailAlloc_2226_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
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
                    v_reuseFailAlloc_2234_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
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
                if leanh::lean_obj_tag(v___x_2245_) == 0 {
                    leanh::lean_dec(v_stx_2184_);
                    v___x_2246_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                    return v___x_2246_;
                } else {
                    v_val_2247_ = leanh::lean_ctor_get(v___x_2245_, 0);
                    v_isSharedCheck_2261_ = (!leanh::lean_is_exclusive(v___x_2245_)) as u8;
                    if v_isSharedCheck_2261_ == 0 {
                        v___x_2249_ = v___x_2245_;
                        v_isShared_2250_ = v_isSharedCheck_2261_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2247_);
                        leanh::lean_dec(v___x_2245_);
                        v___x_2249_ = leanh::lean_box(0);
                        v_isShared_2250_ = v_isSharedCheck_2261_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2251_ = leanh::lean_unsigned_to_nat(4);
                v___x_2252_ = l_Lean_Syntax_getArg(v_stx_2184_, v___x_2251_);
                leanh::lean_dec(v_stx_2184_);
                v___x_2253_ = l_Lean_Syntax_isNone(v___x_2252_);
                if v___x_2253_ == 0 {
                    leanh::lean_inc(v___x_2252_);
                    v___x_2254_ = l_Lean_Syntax_matchesNull(v___x_2252_, v___x_2240_);
                    if v___x_2254_ == 0 {
                        leanh::lean_dec(v___x_2252_);
                        leanh::lean_del_object(v___x_2249_);
                        leanh::lean_dec(v_val_2247_);
                        v___x_2255_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                        return v___x_2255_;
                    } else {
                        v_d_x3f_2256_ = l_Lean_Syntax_getArg(v___x_2252_, v___x_2239_);
                        leanh::lean_dec(v___x_2252_);
                        if v_isShared_2250_ == 0 {
                            leanh::lean_ctor_set(v___x_2249_, 0, v_d_x3f_2256_);
                            v___x_2258_ = v___x_2249_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_2259_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_d_x3f_2256_);
                            v___x_2258_ = v_reuseFailAlloc_2259_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2252_);
                    leanh::lean_del_object(v___x_2249_);
                    v___x_2260_ = leanh::lean_box(0);
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
    mut v_stx_2279_: *mut leanh::LeanObject,
    mut v_a_2280_: *mut leanh::LeanObject,
    mut v_a_2281_: *mut leanh::LeanObject,
    mut v_a_2282_: *mut leanh::LeanObject,
    mut v_a_2283_: *mut leanh::LeanObject,
    mut v_a_2284_: *mut leanh::LeanObject,
    mut v_a_2285_: *mut leanh::LeanObject,
    mut v_a_2286_: *mut leanh::LeanObject,
    mut v_a_2287_: *mut leanh::LeanObject,
    mut v_a_2288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2289_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline(v_stx_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
    leanh::lean_dec(v_a_2287_);
    leanh::lean_dec_ref(v_a_2286_);
    leanh::lean_dec(v_a_2285_);
    leanh::lean_dec_ref(v_a_2284_);
    leanh::lean_dec(v_a_2283_);
    leanh::lean_dec_ref(v_a_2282_);
    leanh::lean_dec(v_a_2281_);
    leanh::lean_dec_ref(v_a_2280_);
    return v_res_2289_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1(
    mut v_as_2290_: *mut leanh::LeanObject,
    mut v_sz_2291_: usize,
    mut v_i_2292_: usize,
    mut v_b_2293_: *mut leanh::LeanObject,
    mut v___y_2294_: *mut leanh::LeanObject,
    mut v___y_2295_: *mut leanh::LeanObject,
    mut v___y_2296_: *mut leanh::LeanObject,
    mut v___y_2297_: *mut leanh::LeanObject,
    mut v___y_2298_: *mut leanh::LeanObject,
    mut v___y_2299_: *mut leanh::LeanObject,
    mut v___y_2300_: *mut leanh::LeanObject,
    mut v___y_2301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___redArg(v_as_2290_, v_sz_2291_, v_i_2292_, v_b_2293_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
    return v___x_2303_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1___boxed(
    mut v_as_2304_: *mut leanh::LeanObject,
    mut v_sz_2305_: *mut leanh::LeanObject,
    mut v_i_2306_: *mut leanh::LeanObject,
    mut v_b_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
    mut v___y_2314_: *mut leanh::LeanObject,
    mut v___y_2315_: *mut leanh::LeanObject,
    mut v___y_2316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2317_: usize = 0;
    let mut v_i_boxed_2318_: usize = 0;
    let mut v_res_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2317_ = leanh::lean_unbox_usize(v_sz_2305_);
    leanh::lean_dec(v_sz_2305_);
    v_i_boxed_2318_ = leanh::lean_unbox_usize(v_i_2306_);
    leanh::lean_dec(v_i_2306_);
    v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline_spec__1(v_as_2304_, v_sz_boxed_2317_, v_i_boxed_2318_, v_b_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
    leanh::lean_dec(v___y_2315_);
    leanh::lean_dec_ref(v___y_2314_);
    leanh::lean_dec(v___y_2313_);
    leanh::lean_dec_ref(v___y_2312_);
    leanh::lean_dec(v___y_2311_);
    leanh::lean_dec_ref(v___y_2310_);
    leanh::lean_dec(v___y_2309_);
    leanh::lean_dec_ref(v___y_2308_);
    leanh::lean_dec_ref(v_as_2304_);
    return v_res_2319_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1()
-> *mut leanh::LeanObject {
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2325_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_2326_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___closed__3;
    v___x_2327_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___closed__1;
    v___x_2328_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2329_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2325_,
        v___x_2326_,
        v___x_2327_,
        v___x_2328_,
    );
    return v___x_2329_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1___boxed(
    mut v_a_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1();
    return v_res_2331_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___lam__0(
    mut v_a_2332_: *mut leanh::LeanObject,
    mut v_a_2333_: *mut leanh::LeanObject,
    mut v___y_2334_: *mut leanh::LeanObject,
    mut v___y_2335_: *mut leanh::LeanObject,
    mut v___y_2336_: *mut leanh::LeanObject,
    mut v___y_2337_: *mut leanh::LeanObject,
    mut v___y_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_2347_: u8 = 0;
    let mut v_contextDependent_2348_: u8 = 0;
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2352_: u8 = 0;
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_unused_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2362_: u8 = 0;
    let mut v_contextDependent_2363_: u8 = 0;
    let mut v_done_2364_: u8 = 0;
    let mut v_e_x27_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2367_: u8 = 0;
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2370_: u8 = 0;
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v_done_2376_: u8 = 0;
    let mut v_contextDependent_2377_: u8 = 0;
    let mut v___y_2379_: u8 = 0;
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_2388_: u8 = 0;
    let mut v_contextDependent_2389_: u8 = 0;
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2397_: u8 = 0;
    let mut v___y_2399_: u8 = 0;
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut v_a_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2410_: u8 = 0;
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2414_: u8 = 0;
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_2343_);
                leanh::lean_inc_ref(v___y_2342_);
                leanh::lean_inc(v___y_2341_);
                leanh::lean_inc_ref(v___y_2340_);
                leanh::lean_inc(v___y_2339_);
                leanh::lean_inc_ref(v___y_2338_);
                leanh::lean_inc(v___y_2337_);
                leanh::lean_inc_ref(v___y_2336_);
                leanh::lean_inc(v___y_2335_);
                leanh::lean_inc_ref(v___y_2334_);
                v___x_2345_ = leanh::lean_apply_11(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2345_) == 0 {
                    v_a_2346_ = leanh::lean_ctor_get(v___x_2345_, 0);
                    leanh::lean_inc(v_a_2346_);
                    if leanh::lean_obj_tag(v_a_2346_) == 0 {
                        v_done_2347_ = leanh::lean_ctor_get_uint8(v_a_2346_, 0 as u32);
                        if v_done_2347_ == 0 {
                            leanh::lean_dec_ref_known(v___x_2345_, 1);
                            v_contextDependent_2348_ =
                                leanh::lean_ctor_get_uint8(v_a_2346_, 1 as u32);
                            leanh::lean_dec_ref_known(v_a_2346_, 0);
                            v___x_2349_ = leanh::lean_apply_11(
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
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_2349_) == 0 {
                                v_a_2350_ = leanh::lean_ctor_get(v___x_2349_, 0);
                                leanh::lean_inc(v_a_2350_);
                                if v_contextDependent_2348_ == 0 {
                                    leanh::lean_dec(v_a_2350_);
                                    return v___x_2349_;
                                } else {
                                    if leanh::lean_obj_tag(v_a_2350_) == 0 {
                                        v_contextDependent_2362_ =
                                            leanh::lean_ctor_get_uint8(v_a_2350_, 1 as u32);
                                        v___y_2352_ = v_contextDependent_2362_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_contextDependent_2363_ =
                                            leanh::lean_ctor_get_uint8(
                                                v_a_2350_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 2
                                                    + 1)
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
                            leanh::lean_dec_ref_known(v_a_2346_, 0);
                            leanh::lean_dec(v___y_2343_);
                            leanh::lean_dec_ref(v___y_2342_);
                            leanh::lean_dec(v___y_2341_);
                            leanh::lean_dec_ref(v___y_2340_);
                            leanh::lean_dec(v___y_2339_);
                            leanh::lean_dec_ref(v___y_2338_);
                            leanh::lean_dec(v___y_2337_);
                            leanh::lean_dec_ref(v___y_2336_);
                            leanh::lean_dec(v___y_2335_);
                            leanh::lean_dec_ref(v___y_2334_);
                            leanh::lean_dec_ref(v_a_2333_);
                            return v___x_2345_;
                        }
                    } else {
                        v_done_2364_ = leanh::lean_ctor_get_uint8(
                            v_a_2346_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        if v_done_2364_ == 0 {
                            leanh::lean_dec_ref_known(v___x_2345_, 1);
                            v_e_x27_2365_ = leanh::lean_ctor_get(v_a_2346_, 0);
                            v_proof_2366_ = leanh::lean_ctor_get(v_a_2346_, 1);
                            v_contextDependent_2367_ = leanh::lean_ctor_get_uint8(
                                v_a_2346_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                    as u32,
                            );
                            v_isSharedCheck_2417_ =
                                (!leanh::lean_is_exclusive(v_a_2346_)) as u8;
                            if v_isSharedCheck_2417_ == 0 {
                                v___x_2369_ = v_a_2346_;
                                v_isShared_2370_ = v_isSharedCheck_2417_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_proof_2366_);
                                leanh::lean_inc(v_e_x27_2365_);
                                leanh::lean_dec(v_a_2346_);
                                v___x_2369_ = leanh::lean_box(0);
                                v_isShared_2370_ = v_isSharedCheck_2417_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_a_2346_, 2);
                            leanh::lean_dec(v___y_2343_);
                            leanh::lean_dec_ref(v___y_2342_);
                            leanh::lean_dec(v___y_2341_);
                            leanh::lean_dec_ref(v___y_2340_);
                            leanh::lean_dec(v___y_2339_);
                            leanh::lean_dec_ref(v___y_2338_);
                            leanh::lean_dec(v___y_2337_);
                            leanh::lean_dec_ref(v___y_2336_);
                            leanh::lean_dec(v___y_2335_);
                            leanh::lean_dec_ref(v___y_2334_);
                            leanh::lean_dec_ref(v_a_2333_);
                            return v___x_2345_;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_2343_);
                    leanh::lean_dec_ref(v___y_2342_);
                    leanh::lean_dec(v___y_2341_);
                    leanh::lean_dec_ref(v___y_2340_);
                    leanh::lean_dec(v___y_2339_);
                    leanh::lean_dec_ref(v___y_2338_);
                    leanh::lean_dec(v___y_2337_);
                    leanh::lean_dec_ref(v___y_2336_);
                    leanh::lean_dec(v___y_2335_);
                    leanh::lean_dec_ref(v___y_2334_);
                    leanh::lean_dec_ref(v_a_2333_);
                    return v___x_2345_;
                }
            }
            1 => {
                if v___y_2352_ == 0 {
                    v_isSharedCheck_2360_ = (!leanh::lean_is_exclusive(v___x_2349_)) as u8;
                    if v_isSharedCheck_2360_ == 0 {
                        v_unused_2361_ = leanh::lean_ctor_get(v___x_2349_, 0);
                        leanh::lean_dec(v_unused_2361_);
                        v___x_2354_ = v___x_2349_;
                        v_isShared_2355_ = v_isSharedCheck_2360_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2349_);
                        v___x_2354_ = leanh::lean_box(0);
                        v_isShared_2355_ = v_isSharedCheck_2360_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2350_);
                    return v___x_2349_;
                }
            }
            2 => {
                v___x_2356_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2350_);
                if v_isShared_2355_ == 0 {
                    leanh::lean_ctor_set(v___x_2354_, 0, v___x_2356_);
                    v___x_2358_ = v___x_2354_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2359_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
                    v___x_2358_ = v_reuseFailAlloc_2359_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2358_;
            }
            4 => {
                leanh::lean_inc(v___y_2343_);
                leanh::lean_inc_ref(v___y_2342_);
                leanh::lean_inc(v___y_2341_);
                leanh::lean_inc_ref(v___y_2340_);
                leanh::lean_inc(v___y_2339_);
                leanh::lean_inc_ref(v_e_x27_2365_);
                v___x_2371_ = leanh::lean_apply_11(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2371_) == 0 {
                    v_a_2372_ = leanh::lean_ctor_get(v___x_2371_, 0);
                    v_isSharedCheck_2416_ = (!leanh::lean_is_exclusive(v___x_2371_)) as u8;
                    if v_isSharedCheck_2416_ == 0 {
                        v___x_2374_ = v___x_2371_;
                        v_isShared_2375_ = v_isSharedCheck_2416_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2372_);
                        leanh::lean_dec(v___x_2371_);
                        v___x_2374_ = leanh::lean_box(0);
                        v_isShared_2375_ = v_isSharedCheck_2416_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2369_);
                    leanh::lean_dec_ref(v_proof_2366_);
                    leanh::lean_dec_ref(v_e_x27_2365_);
                    leanh::lean_dec(v___y_2343_);
                    leanh::lean_dec_ref(v___y_2342_);
                    leanh::lean_dec(v___y_2341_);
                    leanh::lean_dec_ref(v___y_2340_);
                    leanh::lean_dec(v___y_2339_);
                    leanh::lean_dec_ref(v___y_2334_);
                    return v___x_2371_;
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_2372_) == 0 {
                    leanh::lean_dec(v___y_2343_);
                    leanh::lean_dec_ref(v___y_2342_);
                    leanh::lean_dec(v___y_2341_);
                    leanh::lean_dec_ref(v___y_2340_);
                    leanh::lean_dec(v___y_2339_);
                    leanh::lean_dec_ref(v___y_2334_);
                    v_done_2376_ = leanh::lean_ctor_get_uint8(v_a_2372_, 0 as u32);
                    v_contextDependent_2377_ =
                        leanh::lean_ctor_get_uint8(v_a_2372_, 1 as u32);
                    leanh::lean_dec_ref_known(v_a_2372_, 0);
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
                    leanh::lean_del_object(v___x_2374_);
                    leanh::lean_del_object(v___x_2369_);
                    v_e_x27_2386_ = leanh::lean_ctor_get(v_a_2372_, 0);
                    v_proof_2387_ = leanh::lean_ctor_get(v_a_2372_, 1);
                    v_done_2388_ = leanh::lean_ctor_get_uint8(
                        v_a_2372_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_contextDependent_2389_ = leanh::lean_ctor_get_uint8(
                        v_a_2372_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_2415_ = (!leanh::lean_is_exclusive(v_a_2372_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2391_ = v_a_2372_;
                        v_isShared_2392_ = v_isSharedCheck_2415_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_proof_2387_);
                        leanh::lean_inc(v_e_x27_2386_);
                        leanh::lean_dec(v_a_2372_);
                        v___x_2391_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2385_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_e_x27_2365_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_proof_2366_);
                    v___x_2381_ = v_reuseFailAlloc_2385_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2381_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_done_2376_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2381_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_2379_,
                );
                if v_isShared_2375_ == 0 {
                    leanh::lean_ctor_set(v___x_2374_, 0, v___x_2381_);
                    v___x_2383_ = v___x_2374_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2384_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
                    v___x_2383_ = v_reuseFailAlloc_2384_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2383_;
            }
            9 => {
                leanh::lean_inc_ref(v_e_x27_2386_);
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
                leanh::lean_dec(v___y_2343_);
                leanh::lean_dec_ref(v___y_2342_);
                leanh::lean_dec(v___y_2341_);
                leanh::lean_dec_ref(v___y_2340_);
                leanh::lean_dec(v___y_2339_);
                if leanh::lean_obj_tag(v___x_2393_) == 0 {
                    v_a_2394_ = leanh::lean_ctor_get(v___x_2393_, 0);
                    v_isSharedCheck_2406_ = (!leanh::lean_is_exclusive(v___x_2393_)) as u8;
                    if v_isSharedCheck_2406_ == 0 {
                        v___x_2396_ = v___x_2393_;
                        v_isShared_2397_ = v_isSharedCheck_2406_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2394_);
                        leanh::lean_dec(v___x_2393_);
                        v___x_2396_ = leanh::lean_box(0);
                        v_isShared_2397_ = v_isSharedCheck_2406_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2391_);
                    leanh::lean_dec_ref(v_e_x27_2386_);
                    v_a_2407_ = leanh::lean_ctor_get(v___x_2393_, 0);
                    v_isSharedCheck_2414_ = (!leanh::lean_is_exclusive(v___x_2393_)) as u8;
                    if v_isSharedCheck_2414_ == 0 {
                        v___x_2409_ = v___x_2393_;
                        v_isShared_2410_ = v_isSharedCheck_2414_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2407_);
                        leanh::lean_dec(v___x_2393_);
                        v___x_2409_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_2391_, 1, v_a_2394_);
                    v___x_2401_ = v___x_2391_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2405_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_e_x27_2386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_a_2394_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2405_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_done_2388_,
                    );
                    v___x_2401_ = v_reuseFailAlloc_2405_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2401_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_2399_,
                );
                if v_isShared_2397_ == 0 {
                    leanh::lean_ctor_set(v___x_2396_, 0, v___x_2401_);
                    v___x_2403_ = v___x_2396_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2404_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
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
                    v_reuseFailAlloc_2413_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
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
    mut v_a_2418_: *mut leanh::LeanObject,
    mut v_a_2419_: *mut leanh::LeanObject,
    mut v___y_2420_: *mut leanh::LeanObject,
    mut v___y_2421_: *mut leanh::LeanObject,
    mut v___y_2422_: *mut leanh::LeanObject,
    mut v___y_2423_: *mut leanh::LeanObject,
    mut v___y_2424_: *mut leanh::LeanObject,
    mut v___y_2425_: *mut leanh::LeanObject,
    mut v___y_2426_: *mut leanh::LeanObject,
    mut v___y_2427_: *mut leanh::LeanObject,
    mut v___y_2428_: *mut leanh::LeanObject,
    mut v___y_2429_: *mut leanh::LeanObject,
    mut v___y_2430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2431_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___lam__0(v_a_2418_, v_a_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
    return v_res_2431_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen(
    mut v_stx_2439_: *mut leanh::LeanObject,
    mut v_a_2440_: *mut leanh::LeanObject,
    mut v_a_2441_: *mut leanh::LeanObject,
    mut v_a_2442_: *mut leanh::LeanObject,
    mut v_a_2443_: *mut leanh::LeanObject,
    mut v_a_2444_: *mut leanh::LeanObject,
    mut v_a_2445_: *mut leanh::LeanObject,
    mut v_a_2446_: *mut leanh::LeanObject,
    mut v_a_2447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2462_: u8 = 0;
    let mut v___f_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2449_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1;
                leanh::lean_inc(v_stx_2439_);
                v___x_2450_ = l_Lean_Syntax_isOfKind(v_stx_2439_, v___x_2449_);
                if v___x_2450_ == 0 {
                    leanh::lean_dec(v_stx_2439_);
                    v___x_2451_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                    return v___x_2451_;
                } else {
                    v___x_2452_ = leanh::lean_unsigned_to_nat(0);
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
                    if leanh::lean_obj_tag(v___x_2454_) == 0 {
                        v_a_2455_ = leanh::lean_ctor_get(v___x_2454_, 0);
                        leanh::lean_inc(v_a_2455_);
                        leanh::lean_dec_ref_known(v___x_2454_, 1);
                        v___x_2456_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2457_ = l_Lean_Syntax_getArg(v_stx_2439_, v___x_2456_);
                        leanh::lean_dec(v_stx_2439_);
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
                        if leanh::lean_obj_tag(v___x_2458_) == 0 {
                            v_a_2459_ = leanh::lean_ctor_get(v___x_2458_, 0);
                            v_isSharedCheck_2467_ =
                                (!leanh::lean_is_exclusive(v___x_2458_)) as u8;
                            if v_isSharedCheck_2467_ == 0 {
                                v___x_2461_ = v___x_2458_;
                                v_isShared_2462_ = v_isSharedCheck_2467_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2459_);
                                leanh::lean_dec(v___x_2458_);
                                v___x_2461_ = leanh::lean_box(0);
                                v_isShared_2462_ = v_isSharedCheck_2467_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2455_);
                            return v___x_2458_;
                        }
                    } else {
                        leanh::lean_dec(v_stx_2439_);
                        return v___x_2454_;
                    }
                }
            }
            1 => {
                v___f_2463_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                leanh::lean_closure_set(v___f_2463_, 0, v_a_2455_);
                leanh::lean_closure_set(v___f_2463_, 1, v_a_2459_);
                if v_isShared_2462_ == 0 {
                    leanh::lean_ctor_set(v___x_2461_, 0, v___f_2463_);
                    v___x_2465_ = v___x_2461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2466_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___f_2463_);
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
    mut v_stx_2468_: *mut leanh::LeanObject,
    mut v_a_2469_: *mut leanh::LeanObject,
    mut v_a_2470_: *mut leanh::LeanObject,
    mut v_a_2471_: *mut leanh::LeanObject,
    mut v_a_2472_: *mut leanh::LeanObject,
    mut v_a_2473_: *mut leanh::LeanObject,
    mut v_a_2474_: *mut leanh::LeanObject,
    mut v_a_2475_: *mut leanh::LeanObject,
    mut v_a_2476_: *mut leanh::LeanObject,
    mut v_a_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2478_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen(v_stx_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
    leanh::lean_dec(v_a_2476_);
    leanh::lean_dec_ref(v_a_2475_);
    leanh::lean_dec(v_a_2474_);
    leanh::lean_dec_ref(v_a_2473_);
    leanh::lean_dec(v_a_2472_);
    leanh::lean_dec_ref(v_a_2471_);
    leanh::lean_dec(v_a_2470_);
    leanh::lean_dec_ref(v_a_2469_);
    return v_res_2478_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1()
-> *mut leanh::LeanObject {
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2484_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_2485_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___closed__1;
    v___x_2486_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___closed__1;
    v___x_2487_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2488_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2484_,
        v___x_2485_,
        v___x_2486_,
        v___x_2487_,
    );
    return v___x_2488_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1___boxed(
    mut v_a_2489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2490_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1();
    return v_res_2490_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___lam__0(
    mut v_a_2491_: *mut leanh::LeanObject,
    mut v_a_2492_: *mut leanh::LeanObject,
    mut v___y_2493_: *mut leanh::LeanObject,
    mut v___y_2494_: *mut leanh::LeanObject,
    mut v___y_2495_: *mut leanh::LeanObject,
    mut v___y_2496_: *mut leanh::LeanObject,
    mut v___y_2497_: *mut leanh::LeanObject,
    mut v___y_2498_: *mut leanh::LeanObject,
    mut v___y_2499_: *mut leanh::LeanObject,
    mut v___y_2500_: *mut leanh::LeanObject,
    mut v___y_2501_: *mut leanh::LeanObject,
    mut v___y_2502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_2506_: u8 = 0;
    let mut v_contextDependent_2507_: u8 = 0;
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2511_: u8 = 0;
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2519_: u8 = 0;
    let mut v_unused_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2521_: u8 = 0;
    let mut v_contextDependent_2522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_2502_);
                leanh::lean_inc_ref(v___y_2501_);
                leanh::lean_inc(v___y_2500_);
                leanh::lean_inc_ref(v___y_2499_);
                leanh::lean_inc(v___y_2498_);
                leanh::lean_inc_ref(v___y_2497_);
                leanh::lean_inc(v___y_2496_);
                leanh::lean_inc_ref(v___y_2495_);
                leanh::lean_inc(v___y_2494_);
                leanh::lean_inc_ref(v___y_2493_);
                v___x_2504_ = leanh::lean_apply_11(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2504_) == 0 {
                    v_a_2505_ = leanh::lean_ctor_get(v___x_2504_, 0);
                    leanh::lean_inc(v_a_2505_);
                    if leanh::lean_obj_tag(v_a_2505_) == 0 {
                        v_done_2506_ = leanh::lean_ctor_get_uint8(v_a_2505_, 0 as u32);
                        if v_done_2506_ == 0 {
                            leanh::lean_dec_ref_known(v___x_2504_, 1);
                            v_contextDependent_2507_ =
                                leanh::lean_ctor_get_uint8(v_a_2505_, 1 as u32);
                            leanh::lean_dec_ref_known(v_a_2505_, 0);
                            v___x_2508_ = leanh::lean_apply_11(
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
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_2508_) == 0 {
                                v_a_2509_ = leanh::lean_ctor_get(v___x_2508_, 0);
                                leanh::lean_inc(v_a_2509_);
                                if v_contextDependent_2507_ == 0 {
                                    leanh::lean_dec(v_a_2509_);
                                    return v___x_2508_;
                                } else {
                                    if leanh::lean_obj_tag(v_a_2509_) == 0 {
                                        v_contextDependent_2521_ =
                                            leanh::lean_ctor_get_uint8(v_a_2509_, 1 as u32);
                                        v___y_2511_ = v_contextDependent_2521_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_contextDependent_2522_ =
                                            leanh::lean_ctor_get_uint8(
                                                v_a_2509_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 2
                                                    + 1)
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
                            leanh::lean_dec_ref_known(v_a_2505_, 0);
                            leanh::lean_dec(v___y_2502_);
                            leanh::lean_dec_ref(v___y_2501_);
                            leanh::lean_dec(v___y_2500_);
                            leanh::lean_dec_ref(v___y_2499_);
                            leanh::lean_dec(v___y_2498_);
                            leanh::lean_dec_ref(v___y_2497_);
                            leanh::lean_dec(v___y_2496_);
                            leanh::lean_dec_ref(v___y_2495_);
                            leanh::lean_dec(v___y_2494_);
                            leanh::lean_dec_ref(v___y_2493_);
                            leanh::lean_dec_ref(v_a_2492_);
                            return v___x_2504_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_2505_, 2);
                        leanh::lean_dec(v___y_2502_);
                        leanh::lean_dec_ref(v___y_2501_);
                        leanh::lean_dec(v___y_2500_);
                        leanh::lean_dec_ref(v___y_2499_);
                        leanh::lean_dec(v___y_2498_);
                        leanh::lean_dec_ref(v___y_2497_);
                        leanh::lean_dec(v___y_2496_);
                        leanh::lean_dec_ref(v___y_2495_);
                        leanh::lean_dec(v___y_2494_);
                        leanh::lean_dec_ref(v___y_2493_);
                        leanh::lean_dec_ref(v_a_2492_);
                        return v___x_2504_;
                    }
                } else {
                    leanh::lean_dec(v___y_2502_);
                    leanh::lean_dec_ref(v___y_2501_);
                    leanh::lean_dec(v___y_2500_);
                    leanh::lean_dec_ref(v___y_2499_);
                    leanh::lean_dec(v___y_2498_);
                    leanh::lean_dec_ref(v___y_2497_);
                    leanh::lean_dec(v___y_2496_);
                    leanh::lean_dec_ref(v___y_2495_);
                    leanh::lean_dec(v___y_2494_);
                    leanh::lean_dec_ref(v___y_2493_);
                    leanh::lean_dec_ref(v_a_2492_);
                    return v___x_2504_;
                }
            }
            1 => {
                if v___y_2511_ == 0 {
                    v_isSharedCheck_2519_ = (!leanh::lean_is_exclusive(v___x_2508_)) as u8;
                    if v_isSharedCheck_2519_ == 0 {
                        v_unused_2520_ = leanh::lean_ctor_get(v___x_2508_, 0);
                        leanh::lean_dec(v_unused_2520_);
                        v___x_2513_ = v___x_2508_;
                        v_isShared_2514_ = v_isSharedCheck_2519_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2508_);
                        v___x_2513_ = leanh::lean_box(0);
                        v_isShared_2514_ = v_isSharedCheck_2519_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2509_);
                    return v___x_2508_;
                }
            }
            2 => {
                v___x_2515_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2509_);
                if v_isShared_2514_ == 0 {
                    leanh::lean_ctor_set(v___x_2513_, 0, v___x_2515_);
                    v___x_2517_ = v___x_2513_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
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
    mut v_a_2523_: *mut leanh::LeanObject,
    mut v_a_2524_: *mut leanh::LeanObject,
    mut v___y_2525_: *mut leanh::LeanObject,
    mut v___y_2526_: *mut leanh::LeanObject,
    mut v___y_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
    mut v___y_2531_: *mut leanh::LeanObject,
    mut v___y_2532_: *mut leanh::LeanObject,
    mut v___y_2533_: *mut leanh::LeanObject,
    mut v___y_2534_: *mut leanh::LeanObject,
    mut v___y_2535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2536_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___lam__0(v_a_2523_, v_a_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
    return v_res_2536_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse(
    mut v_stx_2544_: *mut leanh::LeanObject,
    mut v_a_2545_: *mut leanh::LeanObject,
    mut v_a_2546_: *mut leanh::LeanObject,
    mut v_a_2547_: *mut leanh::LeanObject,
    mut v_a_2548_: *mut leanh::LeanObject,
    mut v_a_2549_: *mut leanh::LeanObject,
    mut v_a_2550_: *mut leanh::LeanObject,
    mut v_a_2551_: *mut leanh::LeanObject,
    mut v_a_2552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: u8 = 0;
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v___f_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2554_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1;
                leanh::lean_inc(v_stx_2544_);
                v___x_2555_ = l_Lean_Syntax_isOfKind(v_stx_2544_, v___x_2554_);
                if v___x_2555_ == 0 {
                    leanh::lean_dec(v_stx_2544_);
                    v___x_2556_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
                    return v___x_2556_;
                } else {
                    v___x_2557_ = leanh::lean_unsigned_to_nat(0);
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
                    if leanh::lean_obj_tag(v___x_2559_) == 0 {
                        v_a_2560_ = leanh::lean_ctor_get(v___x_2559_, 0);
                        leanh::lean_inc(v_a_2560_);
                        leanh::lean_dec_ref_known(v___x_2559_, 1);
                        v___x_2561_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2562_ = l_Lean_Syntax_getArg(v_stx_2544_, v___x_2561_);
                        leanh::lean_dec(v_stx_2544_);
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
                        if leanh::lean_obj_tag(v___x_2563_) == 0 {
                            v_a_2564_ = leanh::lean_ctor_get(v___x_2563_, 0);
                            v_isSharedCheck_2572_ =
                                (!leanh::lean_is_exclusive(v___x_2563_)) as u8;
                            if v_isSharedCheck_2572_ == 0 {
                                v___x_2566_ = v___x_2563_;
                                v_isShared_2567_ = v_isSharedCheck_2572_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2564_);
                                leanh::lean_dec(v___x_2563_);
                                v___x_2566_ = leanh::lean_box(0);
                                v_isShared_2567_ = v_isSharedCheck_2572_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2560_);
                            return v___x_2563_;
                        }
                    } else {
                        leanh::lean_dec(v_stx_2544_);
                        return v___x_2559_;
                    }
                }
            }
            1 => {
                v___f_2568_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                leanh::lean_closure_set(v___f_2568_, 0, v_a_2560_);
                leanh::lean_closure_set(v___f_2568_, 1, v_a_2564_);
                if v_isShared_2567_ == 0 {
                    leanh::lean_ctor_set(v___x_2566_, 0, v___f_2568_);
                    v___x_2570_ = v___x_2566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___f_2568_);
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
    mut v_stx_2573_: *mut leanh::LeanObject,
    mut v_a_2574_: *mut leanh::LeanObject,
    mut v_a_2575_: *mut leanh::LeanObject,
    mut v_a_2576_: *mut leanh::LeanObject,
    mut v_a_2577_: *mut leanh::LeanObject,
    mut v_a_2578_: *mut leanh::LeanObject,
    mut v_a_2579_: *mut leanh::LeanObject,
    mut v_a_2580_: *mut leanh::LeanObject,
    mut v_a_2581_: *mut leanh::LeanObject,
    mut v_a_2582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2583_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse(v_stx_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
    leanh::lean_dec(v_a_2581_);
    leanh::lean_dec_ref(v_a_2580_);
    leanh::lean_dec(v_a_2579_);
    leanh::lean_dec_ref(v_a_2578_);
    leanh::lean_dec(v_a_2577_);
    leanh::lean_dec_ref(v_a_2576_);
    leanh::lean_dec(v_a_2575_);
    leanh::lean_dec_ref(v_a_2574_);
    return v_res_2583_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1()
-> *mut leanh::LeanObject {
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2589_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_2590_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___closed__1;
    v___x_2591_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___closed__1;
    v___x_2592_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2593_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2589_,
        v___x_2590_,
        v___x_2591_,
        v___x_2592_,
    );
    return v___x_2593_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1___boxed(
    mut v_a_2594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2595_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1();
    return v_res_2595_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen(
    mut v_stx_2603_: *mut leanh::LeanObject,
    mut v_a_2604_: *mut leanh::LeanObject,
    mut v_a_2605_: *mut leanh::LeanObject,
    mut v_a_2606_: *mut leanh::LeanObject,
    mut v_a_2607_: *mut leanh::LeanObject,
    mut v_a_2608_: *mut leanh::LeanObject,
    mut v_a_2609_: *mut leanh::LeanObject,
    mut v_a_2610_: *mut leanh::LeanObject,
    mut v_a_2611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    v___x_2613_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1;
    leanh::lean_inc(v_stx_2603_);
    v___x_2614_ = l_Lean_Syntax_isOfKind(v_stx_2603_, v___x_2613_);
    if v___x_2614_ == 0 {
        let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_2603_);
        v___x_2615_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
        return v___x_2615_;
    } else {
        let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2616_ = leanh::lean_unsigned_to_nat(1);
        v___x_2617_ = l_Lean_Syntax_getArg(v_stx_2603_, v___x_2616_);
        leanh::lean_dec(v_stx_2603_);
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
    mut v_stx_2619_: *mut leanh::LeanObject,
    mut v_a_2620_: *mut leanh::LeanObject,
    mut v_a_2621_: *mut leanh::LeanObject,
    mut v_a_2622_: *mut leanh::LeanObject,
    mut v_a_2623_: *mut leanh::LeanObject,
    mut v_a_2624_: *mut leanh::LeanObject,
    mut v_a_2625_: *mut leanh::LeanObject,
    mut v_a_2626_: *mut leanh::LeanObject,
    mut v_a_2627_: *mut leanh::LeanObject,
    mut v_a_2628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2629_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen(v_stx_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
    leanh::lean_dec(v_a_2627_);
    leanh::lean_dec_ref(v_a_2626_);
    leanh::lean_dec(v_a_2625_);
    leanh::lean_dec_ref(v_a_2624_);
    leanh::lean_dec(v_a_2623_);
    leanh::lean_dec_ref(v_a_2622_);
    leanh::lean_dec(v_a_2621_);
    leanh::lean_dec_ref(v_a_2620_);
    return v_res_2629_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1()
-> *mut leanh::LeanObject {
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2635_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
    v___x_2636_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___closed__1;
    v___x_2637_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___closed__1;
    v___x_2638_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2639_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2635_,
        v___x_2636_,
        v___x_2637_,
        v___x_2638_,
    );
    return v___x_2639_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1___boxed(
    mut v_a_2640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2641_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1();
    return v_res_2641_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2644_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg___closed__0;
    v___x_2645_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2645_, 0, v___x_2644_);
    return v___x_2645_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg___boxed(
    mut v_a_2646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2647_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg();
    return v_res_2647_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf(
    mut v_x_2648_: *mut leanh::LeanObject,
    mut v_a_2649_: *mut leanh::LeanObject,
    mut v_a_2650_: *mut leanh::LeanObject,
    mut v_a_2651_: *mut leanh::LeanObject,
    mut v_a_2652_: *mut leanh::LeanObject,
    mut v_a_2653_: *mut leanh::LeanObject,
    mut v_a_2654_: *mut leanh::LeanObject,
    mut v_a_2655_: *mut leanh::LeanObject,
    mut v_a_2656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2658_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___redArg();
    return v___x_2658_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___boxed(
    mut v_x_2659_: *mut leanh::LeanObject,
    mut v_a_2660_: *mut leanh::LeanObject,
    mut v_a_2661_: *mut leanh::LeanObject,
    mut v_a_2662_: *mut leanh::LeanObject,
    mut v_a_2663_: *mut leanh::LeanObject,
    mut v_a_2664_: *mut leanh::LeanObject,
    mut v_a_2665_: *mut leanh::LeanObject,
    mut v_a_2666_: *mut leanh::LeanObject,
    mut v_a_2667_: *mut leanh::LeanObject,
    mut v_a_2668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2669_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf(v_x_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
    leanh::lean_dec(v_a_2667_);
    leanh::lean_dec_ref(v_a_2666_);
    leanh::lean_dec(v_a_2665_);
    leanh::lean_dec_ref(v_a_2664_);
    leanh::lean_dec(v_a_2663_);
    leanh::lean_dec_ref(v_a_2662_);
    leanh::lean_dec(v_a_2661_);
    leanh::lean_dec_ref(v_a_2660_);
    leanh::lean_dec(v_x_2659_);
    return v_res_2669_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1()
-> *mut leanh::LeanObject {
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2682_ = l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute;
    v___x_2683_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__1;
    v___x_2684_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___closed__3;
    v___x_2685_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2686_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2682_,
        v___x_2683_,
        v___x_2684_,
        v___x_2685_,
    );
    return v___x_2686_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1___boxed(
    mut v_a_2687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2688_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1();
    return v_res_2688_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2690_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0;
    v___x_2691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2691_, 0, v___x_2690_);
    return v___x_2691_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___redArg___boxed(
    mut v_a_2692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2693_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___redArg();
    return v_res_2693_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone(
    mut v_x_2694_: *mut leanh::LeanObject,
    mut v_a_2695_: *mut leanh::LeanObject,
    mut v_a_2696_: *mut leanh::LeanObject,
    mut v_a_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: *mut leanh::LeanObject,
    mut v_a_2699_: *mut leanh::LeanObject,
    mut v_a_2700_: *mut leanh::LeanObject,
    mut v_a_2701_: *mut leanh::LeanObject,
    mut v_a_2702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2704_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___redArg();
    return v___x_2704_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___boxed(
    mut v_x_2705_: *mut leanh::LeanObject,
    mut v_a_2706_: *mut leanh::LeanObject,
    mut v_a_2707_: *mut leanh::LeanObject,
    mut v_a_2708_: *mut leanh::LeanObject,
    mut v_a_2709_: *mut leanh::LeanObject,
    mut v_a_2710_: *mut leanh::LeanObject,
    mut v_a_2711_: *mut leanh::LeanObject,
    mut v_a_2712_: *mut leanh::LeanObject,
    mut v_a_2713_: *mut leanh::LeanObject,
    mut v_a_2714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2715_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone(v_x_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
    leanh::lean_dec(v_a_2713_);
    leanh::lean_dec_ref(v_a_2712_);
    leanh::lean_dec(v_a_2711_);
    leanh::lean_dec_ref(v_a_2710_);
    leanh::lean_dec(v_a_2709_);
    leanh::lean_dec_ref(v_a_2708_);
    leanh::lean_dec(v_a_2707_);
    leanh::lean_dec_ref(v_a_2706_);
    leanh::lean_dec(v_x_2705_);
    return v_res_2715_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1()
-> *mut leanh::LeanObject {
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2728_ = l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute;
    v___x_2729_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__1;
    v___x_2730_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___closed__3;
    v___x_2731_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2732_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2728_,
        v___x_2729_,
        v___x_2730_,
        v___x_2731_,
    );
    return v___x_2732_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1___boxed(
    mut v_a_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2734_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1();
    return v_res_2734_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen(
    mut v_stx_2742_: *mut leanh::LeanObject,
    mut v_a_2743_: *mut leanh::LeanObject,
    mut v_a_2744_: *mut leanh::LeanObject,
    mut v_a_2745_: *mut leanh::LeanObject,
    mut v_a_2746_: *mut leanh::LeanObject,
    mut v_a_2747_: *mut leanh::LeanObject,
    mut v_a_2748_: *mut leanh::LeanObject,
    mut v_a_2749_: *mut leanh::LeanObject,
    mut v_a_2750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: u8 = 0;
    v___x_2752_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1;
    leanh::lean_inc(v_stx_2742_);
    v___x_2753_ = l_Lean_Syntax_isOfKind(v_stx_2742_, v___x_2752_);
    if v___x_2753_ == 0 {
        let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_2742_);
        v___x_2754_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet_spec__0___redArg();
        return v___x_2754_;
    } else {
        let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2755_ = leanh::lean_unsigned_to_nat(1);
        v___x_2756_ = l_Lean_Syntax_getArg(v_stx_2742_, v___x_2755_);
        leanh::lean_dec(v_stx_2742_);
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
    mut v_stx_2758_: *mut leanh::LeanObject,
    mut v_a_2759_: *mut leanh::LeanObject,
    mut v_a_2760_: *mut leanh::LeanObject,
    mut v_a_2761_: *mut leanh::LeanObject,
    mut v_a_2762_: *mut leanh::LeanObject,
    mut v_a_2763_: *mut leanh::LeanObject,
    mut v_a_2764_: *mut leanh::LeanObject,
    mut v_a_2765_: *mut leanh::LeanObject,
    mut v_a_2766_: *mut leanh::LeanObject,
    mut v_a_2767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2768_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen(v_stx_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
    leanh::lean_dec(v_a_2766_);
    leanh::lean_dec_ref(v_a_2765_);
    leanh::lean_dec(v_a_2764_);
    leanh::lean_dec_ref(v_a_2763_);
    leanh::lean_dec(v_a_2762_);
    leanh::lean_dec_ref(v_a_2761_);
    leanh::lean_dec(v_a_2760_);
    leanh::lean_dec_ref(v_a_2759_);
    return v_res_2768_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1()
-> *mut leanh::LeanObject {
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2774_ = l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute;
    v___x_2775_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___closed__1;
    v___x_2776_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___closed__1;
    v___x_2777_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_2778_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2774_,
        v___x_2775_,
        v___x_2776_,
        v___x_2777_,
    );
    return v___x_2778_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1___boxed(
    mut v_a_2779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2780_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1();
    return v_res_2780_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Sym_Simp_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocGround__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocTelescope__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocControl__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocArrowTelescope__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocSelf__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocNone__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteSet__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocRewriteInline__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocAndThen__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocOrElse__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabSimprocParen__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischSelf__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischNone__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen___regBuiltin___private_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin_0__Lean_Elab_Tactic_Grind_elabDischParen__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Sym_Simp_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(builtin);
}
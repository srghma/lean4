// Lean compiler output
// Module: Lean.Elab.PreDefinition.TerminationMeasure
// Imports: Lean.Elab.Binders Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_pop,
    lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_ref_get,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node4, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isSuffixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Elab::Binders::{
    initialize_Lean_Elab_Binders, l_Lean_Elab_Term_elabFunBinders___redArg,
    runtime_initialize_Lean_Elab_Binders,
};
use crate::r#gen::Lean::Elab::SyntheticMVars::l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType___boxed, l_Lean_Elab_Term_instInhabitedTermElabM,
    l_Lean_Elab_Term_withDeclName___redArg, l_Lean_Elab_Term_withoutErrToSorryImp___redArg,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_isLambda, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_andList, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_check;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Basic::{
    l_Lean_PrettyPrinter_Delaborator_delab,
    l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg,
    l_Lean_PrettyPrinter_delabCore___redArg,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_hasIdent;
pub static l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__1_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__0_value)
            as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedTerminationMeasure_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedTerminationMeasure: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [111, 110, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0_value
) as *mut leanh::LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4_value:
    leanh::LeanStringObject<53> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        84, 104, 101, 32, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 32, 109, 101, 97,
        115, 117, 114, 101, 32, 111, 102, 32, 97, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97,
        108, 108, 121, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        102, 117, 110, 99, 116, 105, 111, 110, 32, 109, 117, 115, 116, 32, 98, 101, 32, 111, 110,
        101, 32, 111, 102, 32, 116, 104, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
        32, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8_value:
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
    m_data: [44, 32, 98, 117, 116, 0],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [10, 105, 115, 110, 39, 116, 32, 0],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        111, 110, 101, 32, 111, 102, 32, 116, 104, 101, 115, 101, 46, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116,
        105, 111, 110, 46, 84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 77, 101, 97, 115,
        117, 114, 101, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 101, 114, 109, 105, 110, 97, 116, 105, 111,
        110, 77, 101, 97, 115, 117, 114, 101, 46, 101, 108, 97, 98, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 43,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 101, 120, 116, 114, 97, 80, 97, 114, 97, 109, 115, 32, 226, 137, 164, 32, 97, 114,
        105, 116, 121, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4_value:
    leanh::LeanStringObject<45> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        32, 98, 111, 117, 110, 100, 32, 105, 110, 32, 96, 116, 101, 114, 109, 105, 110, 97, 116,
        105, 111, 110, 95, 98, 121, 96, 44, 32, 98, 117, 116, 32, 116, 104, 101, 32, 98, 111, 100,
        121, 32, 111, 102, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [32, 111, 110, 108, 121, 32, 98, 105, 110, 100, 115, 32, 0],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__10_value:
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
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__10_value)
            as *mut leanh::LeanObject,
        5117844058249666356 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12_value:
    leanh::LeanStringObject<60> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 60,
    m_capacity: 60,
    m_length: 59,
    m_data: [
        32, 40, 83, 105, 110, 99, 101, 32, 76, 101, 97, 110, 32, 118, 52, 46, 54, 46, 48, 44, 32,
        116, 104, 101, 32, 96, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 95, 98, 121,
        96, 32, 99, 108, 97, 117, 115, 101, 32, 110, 111, 32, 108, 111, 110, 103, 101, 114, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__14_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        101, 120, 112, 101, 99, 116, 115, 32, 116, 104, 101, 32, 102, 117, 110, 99, 116, 105, 111,
        110, 32, 110, 97, 109, 101, 32, 104, 101, 114, 101, 46, 41, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 101, 114, 109, 105, 110, 97, 116, 105, 111,
        110, 77, 101, 97, 115, 117, 114, 101, 46, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108,
        65, 114, 103, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1_value:
    leanh::LeanStringObject<65> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 65,
    m_capacity: 65,
    m_length: 64,
    m_data: [
        84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 77, 101, 97, 115, 117, 114, 101, 46,
        115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 65, 114, 103, 58, 32, 98, 111, 100, 121,
        32, 110, 111, 116, 32, 111, 110, 101, 32, 111, 102, 32, 116, 104, 101, 32, 112, 97, 114,
        97, 109, 101, 116, 101, 114, 115, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_structuralArg___closed__0_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 109, 101, 97, 115, 117, 114, 101, 46, 115, 116, 114, 117, 99, 116, 117, 114, 97,
        108, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationMeasure_structuralArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_structuralArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationMeasure_structuralArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_TerminationMeasure_structuralArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationMeasure_structuralArg___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_TerminationMeasure_structuralArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_structuralArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3_value) as *mut leanh::LeanObject;
static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3_value) as *mut leanh::LeanObject,3984140175429830279 as *mut leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 66, 121, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1_value) as *mut leanh::LeanObject,7625897890118033792 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2_value) as *mut leanh::LeanObject,11893284350339308820 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 95, 98, 121, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__5_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = leanh::lean_box(0);
    v___x_1494_ = l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__1;
    v___x_1495_ = l_Lean_Expr_const___override(v___x_1494_, v___x_1493_);
    return v___x_1495_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1496_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2_once
        ),
        _init_l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2,
    );
    v___x_1497_ = 0;
    v___x_1498_ = leanh::lean_box(0);
    v___x_1499_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_1499_, 0, v___x_1498_);
    leanh::lean_ctor_set(v___x_1499_, 1, v___x_1496_);
    leanh::lean_ctor_set_uint8(
        v___x_1499_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_1497_,
    );
    return v___x_1499_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTerminationMeasure_default()
-> *mut leanh::LeanObject {
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3_once
        ),
        _init_l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3,
    );
    return v___x_1500_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTerminationMeasure() -> *mut leanh::LeanObject {
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1501_ = l_Lean_Elab_instInhabitedTerminationMeasure_default;
    return v___x_1501_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__0;
    v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
    return v___x_1504_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1508_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__3;
    v___x_1509_ = l_Lean_MessageData_ofFormat(v___x_1508_);
    return v___x_1509_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(
    mut v_a_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    v___x_1511_ = leanh::lean_unsigned_to_nat(1);
    v___x_1512_ = lean_nat_dec_eq(v_a_1510_, v___x_1511_);
    if v___x_1512_ == 0 {
        let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1513_ = l_Nat_reprFast(v_a_1510_);
        v___x_1514_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1514_, 0, v___x_1513_);
        v___x_1515_ = l_Lean_MessageData_ofFormat(v___x_1514_);
        v___x_1516_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1);
        v___x_1517_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1517_, 0, v___x_1515_);
        leanh::lean_ctor_set(v___x_1517_, 1, v___x_1516_);
        return v___x_1517_;
    } else {
        let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_1510_);
        v___x_1518_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4_once), _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4);
        return v___x_1518_;
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0(
    mut v_k_1519_: *mut leanh::LeanObject,
    mut v___y_1520_: *mut leanh::LeanObject,
    mut v___y_1521_: *mut leanh::LeanObject,
    mut v_b_1522_: *mut leanh::LeanObject,
    mut v_c_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
    mut v___y_1525_: *mut leanh::LeanObject,
    mut v___y_1526_: *mut leanh::LeanObject,
    mut v___y_1527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1527_);
    leanh::lean_inc_ref(v___y_1526_);
    leanh::lean_inc(v___y_1525_);
    leanh::lean_inc_ref(v___y_1524_);
    leanh::lean_inc(v___y_1521_);
    leanh::lean_inc_ref(v___y_1520_);
    v___x_1529_ = leanh::lean_apply_9(
        v_k_1519_,
        v_b_1522_,
        v_c_1523_,
        v___y_1520_,
        v___y_1521_,
        v___y_1524_,
        v___y_1525_,
        v___y_1526_,
        v___y_1527_,
        leanh::lean_box(0),
    );
    return v___x_1529_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0___boxed(
    mut v_k_1530_: *mut leanh::LeanObject,
    mut v___y_1531_: *mut leanh::LeanObject,
    mut v___y_1532_: *mut leanh::LeanObject,
    mut v_b_1533_: *mut leanh::LeanObject,
    mut v_c_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
    mut v___y_1538_: *mut leanh::LeanObject,
    mut v___y_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1540_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0(v_k_1530_, v___y_1531_, v___y_1532_, v_b_1533_, v_c_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
    leanh::lean_dec(v___y_1538_);
    leanh::lean_dec_ref(v___y_1537_);
    leanh::lean_dec(v___y_1536_);
    leanh::lean_dec_ref(v___y_1535_);
    leanh::lean_dec(v___y_1532_);
    leanh::lean_dec_ref(v___y_1531_);
    return v_res_1540_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(
    mut v_type_1541_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_1542_: *mut leanh::LeanObject,
    mut v_k_1543_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1544_: u8,
    mut v_whnfType_1545_: u8,
    mut v___y_1546_: *mut leanh::LeanObject,
    mut v___y_1547_: *mut leanh::LeanObject,
    mut v___y_1548_: *mut leanh::LeanObject,
    mut v___y_1549_: *mut leanh::LeanObject,
    mut v___y_1550_: *mut leanh::LeanObject,
    mut v___y_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1558_: u8 = 0;
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1547_);
                leanh::lean_inc_ref(v___y_1546_);
                v___f_1553_ = leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                leanh::lean_closure_set(v___f_1553_, 0, v_k_1543_);
                leanh::lean_closure_set(v___f_1553_, 1, v___y_1546_);
                leanh::lean_closure_set(v___f_1553_, 2, v___y_1547_);
                v___x_1554_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    leanh::lean_box(0),
                    v_type_1541_,
                    v_maxFVars_x3f_1542_,
                    v___f_1553_,
                    v_cleanupAnnotations_1544_,
                    v_whnfType_1545_,
                    v___y_1548_,
                    v___y_1549_,
                    v___y_1550_,
                    v___y_1551_,
                );
                if leanh::lean_obj_tag(v___x_1554_) == 0 {
                    return v___x_1554_;
                } else {
                    v_a_1555_ = leanh::lean_ctor_get(v___x_1554_, 0);
                    v_isSharedCheck_1562_ = (!leanh::lean_is_exclusive(v___x_1554_)) as u8;
                    if v_isSharedCheck_1562_ == 0 {
                        v___x_1557_ = v___x_1554_;
                        v_isShared_1558_ = v_isSharedCheck_1562_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1555_);
                        leanh::lean_dec(v___x_1554_);
                        v___x_1557_ = leanh::lean_box(0);
                        v_isShared_1558_ = v_isSharedCheck_1562_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1558_ == 0 {
                    v___x_1560_ = v___x_1557_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1561_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
                    v___x_1560_ = v_reuseFailAlloc_1561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___boxed(
    mut v_type_1563_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_1564_: *mut leanh::LeanObject,
    mut v_k_1565_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1566_: *mut leanh::LeanObject,
    mut v_whnfType_1567_: *mut leanh::LeanObject,
    mut v___y_1568_: *mut leanh::LeanObject,
    mut v___y_1569_: *mut leanh::LeanObject,
    mut v___y_1570_: *mut leanh::LeanObject,
    mut v___y_1571_: *mut leanh::LeanObject,
    mut v___y_1572_: *mut leanh::LeanObject,
    mut v___y_1573_: *mut leanh::LeanObject,
    mut v___y_1574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1575_: u8 = 0;
    let mut v_whnfType_boxed_1576_: u8 = 0;
    let mut v_res_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1575_ = (leanh::lean_unbox(v_cleanupAnnotations_1566_) as u8);
    v_whnfType_boxed_1576_ = (leanh::lean_unbox(v_whnfType_1567_) as u8);
    v_res_1577_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v_type_1563_, v_maxFVars_x3f_1564_, v_k_1565_, v_cleanupAnnotations_boxed_1575_, v_whnfType_boxed_1576_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
    leanh::lean_dec(v___y_1573_);
    leanh::lean_dec_ref(v___y_1572_);
    leanh::lean_dec(v___y_1571_);
    leanh::lean_dec_ref(v___y_1570_);
    leanh::lean_dec(v___y_1569_);
    leanh::lean_dec_ref(v___y_1568_);
    return v_res_1577_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0(
    mut v_00_u03b1_1578_: *mut leanh::LeanObject,
    mut v_type_1579_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_1580_: *mut leanh::LeanObject,
    mut v_k_1581_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1582_: u8,
    mut v_whnfType_1583_: u8,
    mut v___y_1584_: *mut leanh::LeanObject,
    mut v___y_1585_: *mut leanh::LeanObject,
    mut v___y_1586_: *mut leanh::LeanObject,
    mut v___y_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v_type_1579_, v_maxFVars_x3f_1580_, v_k_1581_, v_cleanupAnnotations_1582_, v_whnfType_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
    return v___x_1591_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___boxed(
    mut v_00_u03b1_1592_: *mut leanh::LeanObject,
    mut v_type_1593_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_1594_: *mut leanh::LeanObject,
    mut v_k_1595_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1596_: *mut leanh::LeanObject,
    mut v_whnfType_1597_: *mut leanh::LeanObject,
    mut v___y_1598_: *mut leanh::LeanObject,
    mut v___y_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
    mut v___y_1601_: *mut leanh::LeanObject,
    mut v___y_1602_: *mut leanh::LeanObject,
    mut v___y_1603_: *mut leanh::LeanObject,
    mut v___y_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1605_: u8 = 0;
    let mut v_whnfType_boxed_1606_: u8 = 0;
    let mut v_res_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1605_ = (leanh::lean_unbox(v_cleanupAnnotations_1596_) as u8);
    v_whnfType_boxed_1606_ = (leanh::lean_unbox(v_whnfType_1597_) as u8);
    v_res_1607_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0(
            v_00_u03b1_1592_,
            v_type_1593_,
            v_maxFVars_x3f_1594_,
            v_k_1595_,
            v_cleanupAnnotations_boxed_1605_,
            v_whnfType_boxed_1606_,
            v___y_1598_,
            v___y_1599_,
            v___y_1600_,
            v___y_1601_,
            v___y_1602_,
            v___y_1603_,
        );
    leanh::lean_dec(v___y_1603_);
    leanh::lean_dec_ref(v___y_1602_);
    leanh::lean_dec(v___y_1601_);
    leanh::lean_dec_ref(v___y_1600_);
    leanh::lean_dec(v___y_1599_);
    leanh::lean_dec_ref(v___y_1598_);
    return v_res_1607_;
}
pub unsafe fn l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__1(
    mut v_msg_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = l_Lean_instInhabitedExpr;
    v___x_1610_ = lean_panic_fn_borrowed(v___x_1609_, v_msg_1608_);
    return v___x_1610_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg(
    mut v_a_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
    mut v___y_1613_: *mut leanh::LeanObject,
    mut v___y_1614_: *mut leanh::LeanObject,
    mut v___y_1615_: *mut leanh::LeanObject,
    mut v___y_1616_: *mut leanh::LeanObject,
    mut v___y_1617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1619_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_1611_,
        v___y_1612_,
        v___y_1613_,
        v___y_1614_,
        v___y_1615_,
        v___y_1616_,
        v___y_1617_,
    );
    return v___x_1619_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg___boxed(
    mut v_a_1620_: *mut leanh::LeanObject,
    mut v___y_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
    mut v___y_1623_: *mut leanh::LeanObject,
    mut v___y_1624_: *mut leanh::LeanObject,
    mut v___y_1625_: *mut leanh::LeanObject,
    mut v___y_1626_: *mut leanh::LeanObject,
    mut v___y_1627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1628_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg(v_a_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
    leanh::lean_dec(v___y_1626_);
    leanh::lean_dec_ref(v___y_1625_);
    leanh::lean_dec(v___y_1624_);
    leanh::lean_dec_ref(v___y_1623_);
    leanh::lean_dec(v___y_1622_);
    leanh::lean_dec_ref(v___y_1621_);
    return v_res_1628_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5(
    mut v_00_u03b1_1629_: *mut leanh::LeanObject,
    mut v_a_1630_: *mut leanh::LeanObject,
    mut v___y_1631_: *mut leanh::LeanObject,
    mut v___y_1632_: *mut leanh::LeanObject,
    mut v___y_1633_: *mut leanh::LeanObject,
    mut v___y_1634_: *mut leanh::LeanObject,
    mut v___y_1635_: *mut leanh::LeanObject,
    mut v___y_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_1630_,
        v___y_1631_,
        v___y_1632_,
        v___y_1633_,
        v___y_1634_,
        v___y_1635_,
        v___y_1636_,
    );
    return v___x_1638_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___boxed(
    mut v_00_u03b1_1639_: *mut leanh::LeanObject,
    mut v_a_1640_: *mut leanh::LeanObject,
    mut v___y_1641_: *mut leanh::LeanObject,
    mut v___y_1642_: *mut leanh::LeanObject,
    mut v___y_1643_: *mut leanh::LeanObject,
    mut v___y_1644_: *mut leanh::LeanObject,
    mut v___y_1645_: *mut leanh::LeanObject,
    mut v___y_1646_: *mut leanh::LeanObject,
    mut v___y_1647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1648_ =
        l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5(
            v_00_u03b1_1639_,
            v_a_1640_,
            v___y_1641_,
            v___y_1642_,
            v___y_1643_,
            v___y_1644_,
            v___y_1645_,
            v___y_1646_,
        );
    leanh::lean_dec(v___y_1646_);
    leanh::lean_dec_ref(v___y_1645_);
    leanh::lean_dec(v___y_1644_);
    leanh::lean_dec_ref(v___y_1643_);
    leanh::lean_dec(v___y_1642_);
    leanh::lean_dec_ref(v___y_1641_);
    return v_res_1648_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1649_ = l_Lean_Elab_Term_instInhabitedTermElabM(leanh::lean_box(0));
    return v___x_1649_;
}
pub unsafe fn l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(
    mut v_msg_1650_: *mut leanh::LeanObject,
    mut v___y_1651_: *mut leanh::LeanObject,
    mut v___y_1652_: *mut leanh::LeanObject,
    mut v___y_1653_: *mut leanh::LeanObject,
    mut v___y_1654_: *mut leanh::LeanObject,
    mut v___y_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762__overap_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1658_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0_once
        ),
        _init_l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0,
    );
    v___x_3762__overap_1659_ = lean_panic_fn_borrowed(v___x_1658_, v_msg_1650_);
    leanh::lean_inc(v___y_1656_);
    leanh::lean_inc_ref(v___y_1655_);
    leanh::lean_inc(v___y_1654_);
    leanh::lean_inc_ref(v___y_1653_);
    leanh::lean_inc(v___y_1652_);
    leanh::lean_inc_ref(v___y_1651_);
    v___x_1660_ = leanh::lean_apply_7(
        v___x_3762__overap_1659_,
        v___y_1651_,
        v___y_1652_,
        v___y_1653_,
        v___y_1654_,
        v___y_1655_,
        v___y_1656_,
        leanh::lean_box(0),
    );
    return v___x_1660_;
}
pub unsafe fn l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___boxed(
    mut v_msg_1661_: *mut leanh::LeanObject,
    mut v___y_1662_: *mut leanh::LeanObject,
    mut v___y_1663_: *mut leanh::LeanObject,
    mut v___y_1664_: *mut leanh::LeanObject,
    mut v___y_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
    mut v___y_1667_: *mut leanh::LeanObject,
    mut v___y_1668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1669_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(
        v_msg_1661_,
        v___y_1662_,
        v___y_1663_,
        v___y_1664_,
        v___y_1665_,
        v___y_1666_,
        v___y_1667_,
    );
    leanh::lean_dec(v___y_1667_);
    leanh::lean_dec_ref(v___y_1666_);
    leanh::lean_dec(v___y_1665_);
    leanh::lean_dec_ref(v___y_1664_);
    leanh::lean_dec(v___y_1663_);
    leanh::lean_dec_ref(v___y_1662_);
    return v_res_1669_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_elab___lam__0(
    mut v_ys_1670_: *mut leanh::LeanObject,
    mut v_xs_1671_: *mut leanh::LeanObject,
    mut v_a_1672_: *mut leanh::LeanObject,
    mut v___x_1673_: u8,
    mut v_zs_1674_: *mut leanh::LeanObject,
    mut v_x_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
    mut v___y_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Array_append___redArg(v_ys_1670_, v_xs_1671_);
    v___x_1684_ = l_Array_append___redArg(v___x_1683_, v_zs_1674_);
    v___x_1685_ = 0;
    v___x_1686_ = 1;
    v___x_1687_ = l_Lean_Meta_mkLambdaFVars(
        v___x_1684_,
        v_a_1672_,
        v___x_1685_,
        v___x_1673_,
        v___x_1685_,
        v___x_1673_,
        v___x_1686_,
        v___y_1678_,
        v___y_1679_,
        v___y_1680_,
        v___y_1681_,
    );
    leanh::lean_dec_ref(v___x_1684_);
    return v___x_1687_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_elab___lam__0___boxed(
    mut v_ys_1688_: *mut leanh::LeanObject,
    mut v_xs_1689_: *mut leanh::LeanObject,
    mut v_a_1690_: *mut leanh::LeanObject,
    mut v___x_1691_: *mut leanh::LeanObject,
    mut v_zs_1692_: *mut leanh::LeanObject,
    mut v_x_1693_: *mut leanh::LeanObject,
    mut v___y_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
    mut v___y_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6101__boxed_1701_: u8 = 0;
    let mut v_res_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6101__boxed_1701_ = (leanh::lean_unbox(v___x_1691_) as u8);
    v_res_1702_ = l_Lean_Elab_TerminationMeasure_elab___lam__0(
        v_ys_1688_,
        v_xs_1689_,
        v_a_1690_,
        v___x_6101__boxed_1701_,
        v_zs_1692_,
        v_x_1693_,
        v___y_1694_,
        v___y_1695_,
        v___y_1696_,
        v___y_1697_,
        v___y_1698_,
        v___y_1699_,
    );
    leanh::lean_dec(v___y_1699_);
    leanh::lean_dec_ref(v___y_1698_);
    leanh::lean_dec(v___y_1697_);
    leanh::lean_dec_ref(v___y_1696_);
    leanh::lean_dec(v___y_1695_);
    leanh::lean_dec_ref(v___y_1694_);
    leanh::lean_dec_ref(v_x_1693_);
    leanh::lean_dec_ref(v_zs_1692_);
    leanh::lean_dec_ref(v_xs_1689_);
    return v_res_1702_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1703_ = leanh::lean_box(1);
    v___x_1704_ = l_Lean_MessageData_ofFormat(v___x_1703_);
    return v___x_1704_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__2;
    v___x_1709_ = l_Lean_MessageData_ofFormat(v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11(
    mut v_x_1710_: *mut leanh::LeanObject,
    mut v_x_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1716_: u8 = 0;
    let mut v_before_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1720_: u8 = 0;
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1733_: u8 = 0;
    let mut v_unused_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1711_) == 0 {
                    return v_x_1710_;
                } else {
                    v_head_1712_ = leanh::lean_ctor_get(v_x_1711_, 0);
                    v_tail_1713_ = leanh::lean_ctor_get(v_x_1711_, 1);
                    v_isSharedCheck_1735_ = (!leanh::lean_is_exclusive(v_x_1711_)) as u8;
                    if v_isSharedCheck_1735_ == 0 {
                        v___x_1715_ = v_x_1711_;
                        v_isShared_1716_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1713_);
                        leanh::lean_inc(v_head_1712_);
                        leanh::lean_dec(v_x_1711_);
                        v___x_1715_ = leanh::lean_box(0);
                        v_isShared_1716_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1717_ = leanh::lean_ctor_get(v_head_1712_, 0);
                v_isSharedCheck_1733_ = (!leanh::lean_is_exclusive(v_head_1712_)) as u8;
                if v_isSharedCheck_1733_ == 0 {
                    v_unused_1734_ = leanh::lean_ctor_get(v_head_1712_, 1);
                    leanh::lean_dec(v_unused_1734_);
                    v___x_1719_ = v_head_1712_;
                    v_isShared_1720_ = v_isSharedCheck_1733_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_1717_);
                    leanh::lean_dec(v_head_1712_);
                    v___x_1719_ = leanh::lean_box(0);
                    v_isShared_1720_ = v_isSharedCheck_1733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1721_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0);
                if v_isShared_1720_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1719_, 7);
                    leanh::lean_ctor_set(v___x_1719_, 1, v___x_1721_);
                    leanh::lean_ctor_set(v___x_1719_, 0, v_x_1710_);
                    v___x_1723_ = v___x_1719_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1732_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_x_1710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1721_);
                    v___x_1723_ = v_reuseFailAlloc_1732_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1724_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3);
                if v_isShared_1716_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1715_, 7);
                    leanh::lean_ctor_set(v___x_1715_, 1, v___x_1724_);
                    leanh::lean_ctor_set(v___x_1715_, 0, v___x_1723_);
                    v___x_1726_ = v___x_1715_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1731_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1723_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 1, v___x_1724_);
                    v___x_1726_ = v_reuseFailAlloc_1731_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1727_ = l_Lean_MessageData_ofSyntax(v_before_1717_);
                v___x_1728_ = l_Lean_indentD(v___x_1727_);
                v___x_1729_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1729_, 0, v___x_1726_);
                leanh::lean_ctor_set(v___x_1729_, 1, v___x_1728_);
                v_x_1710_ = v___x_1729_;
                v_x_1711_ = v_tail_1713_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(
    mut v_opts_1736_: *mut leanh::LeanObject,
    mut v_opt_1737_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1738_ = leanh::lean_ctor_get(v_opt_1737_, 0);
    v_defValue_1739_ = leanh::lean_ctor_get(v_opt_1737_, 1);
    v_map_1740_ = leanh::lean_ctor_get(v_opts_1736_, 0);
    v___x_1741_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1740_,
            v_name_1738_,
        );
    if leanh::lean_obj_tag(v___x_1741_) == 0 {
        let mut v___x_1742_: u8 = 0;
        v___x_1742_ = (leanh::lean_unbox(v_defValue_1739_) as u8);
        return v___x_1742_;
    } else {
        let mut v_val_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1743_ = leanh::lean_ctor_get(v___x_1741_, 0);
        leanh::lean_inc(v_val_1743_);
        leanh::lean_dec_ref_known(v___x_1741_, 1);
        if leanh::lean_obj_tag(v_val_1743_) == 1 {
            let mut v_v_1744_: u8 = 0;
            v_v_1744_ = leanh::lean_ctor_get_uint8(v_val_1743_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1743_, 0);
            return v_v_1744_;
        } else {
            let mut v___x_1745_: u8 = 0;
            leanh::lean_dec(v_val_1743_);
            v___x_1745_ = (leanh::lean_unbox(v_defValue_1739_) as u8);
            return v___x_1745_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10___boxed(
    mut v_opts_1746_: *mut leanh::LeanObject,
    mut v_opt_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1748_: u8 = 0;
    let mut v_r_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1748_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(v_opts_1746_, v_opt_1747_);
    leanh::lean_dec_ref(v_opt_1747_);
    leanh::lean_dec_ref(v_opts_1746_);
    v_r_1749_ = leanh::lean_box((v_res_1748_) as usize);
    return v_r_1749_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__1;
    v___x_1754_ = l_Lean_MessageData_ofFormat(v___x_1753_);
    return v___x_1754_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(
    mut v_msgData_1755_: *mut leanh::LeanObject,
    mut v_macroStack_1756_: *mut leanh::LeanObject,
    mut v___y_1757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1768_: u8 = 0;
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1780_: u8 = 0;
    let mut v_unused_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1759_ = leanh::lean_ctor_get(v___y_1757_, 2);
                v___x_1760_ = l_Lean_Elab_pp_macroStack;
                v___x_1761_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(v_options_1759_, v___x_1760_);
                if v___x_1761_ == 0 {
                    leanh::lean_dec(v_macroStack_1756_);
                    v___x_1762_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1762_, 0, v_msgData_1755_);
                    return v___x_1762_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_1756_) == 0 {
                        v___x_1763_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1763_, 0, v_msgData_1755_);
                        return v___x_1763_;
                    } else {
                        v_head_1764_ = leanh::lean_ctor_get(v_macroStack_1756_, 0);
                        leanh::lean_inc(v_head_1764_);
                        v_after_1765_ = leanh::lean_ctor_get(v_head_1764_, 1);
                        v_isSharedCheck_1780_ =
                            (!leanh::lean_is_exclusive(v_head_1764_)) as u8;
                        if v_isSharedCheck_1780_ == 0 {
                            v_unused_1781_ = leanh::lean_ctor_get(v_head_1764_, 0);
                            leanh::lean_dec(v_unused_1781_);
                            v___x_1767_ = v_head_1764_;
                            v_isShared_1768_ = v_isSharedCheck_1780_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_1765_);
                            leanh::lean_dec(v_head_1764_);
                            v___x_1767_ = leanh::lean_box(0);
                            v_isShared_1768_ = v_isSharedCheck_1780_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1769_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0);
                if v_isShared_1768_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1767_, 7);
                    leanh::lean_ctor_set(v___x_1767_, 1, v___x_1769_);
                    leanh::lean_ctor_set(v___x_1767_, 0, v_msgData_1755_);
                    v___x_1771_ = v___x_1767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1779_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_msgData_1755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 1, v___x_1769_);
                    v___x_1771_ = v_reuseFailAlloc_1779_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1772_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2);
                v___x_1773_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1773_, 0, v___x_1771_);
                leanh::lean_ctor_set(v___x_1773_, 1, v___x_1772_);
                v___x_1774_ = l_Lean_MessageData_ofSyntax(v_after_1765_);
                v___x_1775_ = l_Lean_indentD(v___x_1774_);
                v_msgData_1776_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_1776_, 0, v___x_1773_);
                leanh::lean_ctor_set(v_msgData_1776_, 1, v___x_1775_);
                v___x_1777_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11(v_msgData_1776_, v_macroStack_1756_);
                v___x_1778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1778_, 0, v___x_1777_);
                return v___x_1778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___boxed(
    mut v_msgData_1782_: *mut leanh::LeanObject,
    mut v_macroStack_1783_: *mut leanh::LeanObject,
    mut v___y_1784_: *mut leanh::LeanObject,
    mut v___y_1785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_msgData_1782_, v_macroStack_1783_, v___y_1784_);
    leanh::lean_dec_ref(v___y_1784_);
    return v_res_1786_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(
    mut v_msgData_1787_: *mut leanh::LeanObject,
    mut v___y_1788_: *mut leanh::LeanObject,
    mut v___y_1789_: *mut leanh::LeanObject,
    mut v___y_1790_: *mut leanh::LeanObject,
    mut v___y_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1793_ = lean_st_ref_get(v___y_1791_);
    v_env_1794_ = leanh::lean_ctor_get(v___x_1793_, 0);
    leanh::lean_inc_ref(v_env_1794_);
    leanh::lean_dec(v___x_1793_);
    v___x_1795_ = lean_st_ref_get(v___y_1789_);
    v_mctx_1796_ = leanh::lean_ctor_get(v___x_1795_, 0);
    leanh::lean_inc_ref(v_mctx_1796_);
    leanh::lean_dec(v___x_1795_);
    v_lctx_1797_ = leanh::lean_ctor_get(v___y_1788_, 2);
    v_options_1798_ = leanh::lean_ctor_get(v___y_1790_, 2);
    leanh::lean_inc_ref(v_options_1798_);
    leanh::lean_inc_ref(v_lctx_1797_);
    v___x_1799_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1799_, 0, v_env_1794_);
    leanh::lean_ctor_set(v___x_1799_, 1, v_mctx_1796_);
    leanh::lean_ctor_set(v___x_1799_, 2, v_lctx_1797_);
    leanh::lean_ctor_set(v___x_1799_, 3, v_options_1798_);
    v___x_1800_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1800_, 0, v___x_1799_);
    leanh::lean_ctor_set(v___x_1800_, 1, v_msgData_1787_);
    v___x_1801_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    return v___x_1801_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8___boxed(
    mut v_msgData_1802_: *mut leanh::LeanObject,
    mut v___y_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
    mut v___y_1805_: *mut leanh::LeanObject,
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1808_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msgData_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
    leanh::lean_dec(v___y_1806_);
    leanh::lean_dec_ref(v___y_1805_);
    leanh::lean_dec(v___y_1804_);
    leanh::lean_dec_ref(v___y_1803_);
    return v_res_1808_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(
    mut v_msg_1809_: *mut leanh::LeanObject,
    mut v___y_1810_: *mut leanh::LeanObject,
    mut v___y_1811_: *mut leanh::LeanObject,
    mut v___y_1812_: *mut leanh::LeanObject,
    mut v___y_1813_: *mut leanh::LeanObject,
    mut v___y_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1826_: u8 = 0;
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1817_ = leanh::lean_ctor_get(v___y_1814_, 5);
                v___x_1818_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msg_1809_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
                v_a_1819_ = leanh::lean_ctor_get(v___x_1818_, 0);
                leanh::lean_inc(v_a_1819_);
                leanh::lean_dec_ref(v___x_1818_);
                v_macroStack_1820_ = leanh::lean_ctor_get(v___y_1810_, 1);
                v___x_1821_ = l_Lean_Elab_getBetterRef(v_ref_1817_, v_macroStack_1820_);
                leanh::lean_inc(v_macroStack_1820_);
                v___x_1822_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_a_1819_, v_macroStack_1820_, v___y_1814_);
                v_a_1823_ = leanh::lean_ctor_get(v___x_1822_, 0);
                v_isSharedCheck_1831_ = (!leanh::lean_is_exclusive(v___x_1822_)) as u8;
                if v_isSharedCheck_1831_ == 0 {
                    v___x_1825_ = v___x_1822_;
                    v_isShared_1826_ = v_isSharedCheck_1831_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1823_);
                    leanh::lean_dec(v___x_1822_);
                    v___x_1825_ = leanh::lean_box(0);
                    v_isShared_1826_ = v_isSharedCheck_1831_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1827_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1827_, 0, v___x_1821_);
                leanh::lean_ctor_set(v___x_1827_, 1, v_a_1823_);
                if v_isShared_1826_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1825_, 1);
                    leanh::lean_ctor_set(v___x_1825_, 0, v___x_1827_);
                    v___x_1829_ = v___x_1825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
                    v___x_1829_ = v_reuseFailAlloc_1830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg___boxed(
    mut v_msg_1832_: *mut leanh::LeanObject,
    mut v___y_1833_: *mut leanh::LeanObject,
    mut v___y_1834_: *mut leanh::LeanObject,
    mut v___y_1835_: *mut leanh::LeanObject,
    mut v___y_1836_: *mut leanh::LeanObject,
    mut v___y_1837_: *mut leanh::LeanObject,
    mut v___y_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1840_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
    leanh::lean_dec(v___y_1838_);
    leanh::lean_dec_ref(v___y_1837_);
    leanh::lean_dec(v___y_1836_);
    leanh::lean_dec_ref(v___y_1835_);
    leanh::lean_dec(v___y_1834_);
    leanh::lean_dec_ref(v___y_1833_);
    return v_res_1840_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(
    mut v_ref_1841_: *mut leanh::LeanObject,
    mut v_msg_1842_: *mut leanh::LeanObject,
    mut v___y_1843_: *mut leanh::LeanObject,
    mut v___y_1844_: *mut leanh::LeanObject,
    mut v___y_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1862_: u8 = 0;
    let mut v_cancelTk_x3f_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1864_: u8 = 0;
    let mut v_inheritedTraceOptions_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1850_ = leanh::lean_ctor_get(v___y_1847_, 0);
    v_fileMap_1851_ = leanh::lean_ctor_get(v___y_1847_, 1);
    v_options_1852_ = leanh::lean_ctor_get(v___y_1847_, 2);
    v_currRecDepth_1853_ = leanh::lean_ctor_get(v___y_1847_, 3);
    v_maxRecDepth_1854_ = leanh::lean_ctor_get(v___y_1847_, 4);
    v_ref_1855_ = leanh::lean_ctor_get(v___y_1847_, 5);
    v_currNamespace_1856_ = leanh::lean_ctor_get(v___y_1847_, 6);
    v_openDecls_1857_ = leanh::lean_ctor_get(v___y_1847_, 7);
    v_initHeartbeats_1858_ = leanh::lean_ctor_get(v___y_1847_, 8);
    v_maxHeartbeats_1859_ = leanh::lean_ctor_get(v___y_1847_, 9);
    v_quotContext_1860_ = leanh::lean_ctor_get(v___y_1847_, 10);
    v_currMacroScope_1861_ = leanh::lean_ctor_get(v___y_1847_, 11);
    v_diag_1862_ = leanh::lean_ctor_get_uint8(
        v___y_1847_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1863_ = leanh::lean_ctor_get(v___y_1847_, 12);
    v_suppressElabErrors_1864_ = leanh::lean_ctor_get_uint8(
        v___y_1847_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1865_ = leanh::lean_ctor_get(v___y_1847_, 13);
    v_ref_1866_ = l_Lean_replaceRef(v_ref_1841_, v_ref_1855_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1865_);
    leanh::lean_inc(v_cancelTk_x3f_1863_);
    leanh::lean_inc(v_currMacroScope_1861_);
    leanh::lean_inc(v_quotContext_1860_);
    leanh::lean_inc(v_maxHeartbeats_1859_);
    leanh::lean_inc(v_initHeartbeats_1858_);
    leanh::lean_inc(v_openDecls_1857_);
    leanh::lean_inc(v_currNamespace_1856_);
    leanh::lean_inc(v_maxRecDepth_1854_);
    leanh::lean_inc(v_currRecDepth_1853_);
    leanh::lean_inc_ref(v_options_1852_);
    leanh::lean_inc_ref(v_fileMap_1851_);
    leanh::lean_inc_ref(v_fileName_1850_);
    v___x_1867_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1867_, 0, v_fileName_1850_);
    leanh::lean_ctor_set(v___x_1867_, 1, v_fileMap_1851_);
    leanh::lean_ctor_set(v___x_1867_, 2, v_options_1852_);
    leanh::lean_ctor_set(v___x_1867_, 3, v_currRecDepth_1853_);
    leanh::lean_ctor_set(v___x_1867_, 4, v_maxRecDepth_1854_);
    leanh::lean_ctor_set(v___x_1867_, 5, v_ref_1866_);
    leanh::lean_ctor_set(v___x_1867_, 6, v_currNamespace_1856_);
    leanh::lean_ctor_set(v___x_1867_, 7, v_openDecls_1857_);
    leanh::lean_ctor_set(v___x_1867_, 8, v_initHeartbeats_1858_);
    leanh::lean_ctor_set(v___x_1867_, 9, v_maxHeartbeats_1859_);
    leanh::lean_ctor_set(v___x_1867_, 10, v_quotContext_1860_);
    leanh::lean_ctor_set(v___x_1867_, 11, v_currMacroScope_1861_);
    leanh::lean_ctor_set(v___x_1867_, 12, v_cancelTk_x3f_1863_);
    leanh::lean_ctor_set(v___x_1867_, 13, v_inheritedTraceOptions_1865_);
    leanh::lean_ctor_set_uint8(
        v___x_1867_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1862_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1867_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1864_,
    );
    v___x_1868_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___x_1867_, v___y_1848_);
    leanh::lean_dec_ref_known(v___x_1867_, 14);
    return v___x_1868_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg___boxed(
    mut v_ref_1869_: *mut leanh::LeanObject,
    mut v_msg_1870_: *mut leanh::LeanObject,
    mut v___y_1871_: *mut leanh::LeanObject,
    mut v___y_1872_: *mut leanh::LeanObject,
    mut v___y_1873_: *mut leanh::LeanObject,
    mut v___y_1874_: *mut leanh::LeanObject,
    mut v___y_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1878_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(
        v_ref_1869_,
        v_msg_1870_,
        v___y_1871_,
        v___y_1872_,
        v___y_1873_,
        v___y_1874_,
        v___y_1875_,
        v___y_1876_,
    );
    leanh::lean_dec(v___y_1876_);
    leanh::lean_dec_ref(v___y_1875_);
    leanh::lean_dec(v___y_1874_);
    leanh::lean_dec_ref(v___y_1873_);
    leanh::lean_dec(v___y_1872_);
    leanh::lean_dec_ref(v___y_1871_);
    leanh::lean_dec(v_ref_1869_);
    return v_res_1878_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(
    mut v_a_1879_: *mut leanh::LeanObject,
    mut v_as_1880_: *mut leanh::LeanObject,
    mut v_i_1881_: usize,
    mut v_stop_1882_: usize,
) -> u8 {
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: usize = 0;
    let mut v___x_1887_: usize = 0;
    let mut v___x_1889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1883_ = lean_usize_dec_eq(v_i_1881_, v_stop_1882_);
                if v___x_1883_ == 0 {
                    v___x_1884_ = lean_array_uget_borrowed(v_as_1880_, v_i_1881_);
                    v___x_1885_ = lean_expr_eqv(v_a_1879_, v___x_1884_);
                    if v___x_1885_ == 0 {
                        v___x_1886_ = 1usize;
                        v___x_1887_ = lean_usize_add(v_i_1881_, v___x_1886_);
                        v_i_1881_ = v___x_1887_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1885_;
                    }
                } else {
                    v___x_1889_ = 0;
                    return v___x_1889_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2___boxed(
    mut v_a_1890_: *mut leanh::LeanObject,
    mut v_as_1891_: *mut leanh::LeanObject,
    mut v_i_1892_: *mut leanh::LeanObject,
    mut v_stop_1893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1894_: usize = 0;
    let mut v_stop_boxed_1895_: usize = 0;
    let mut v_res_1896_: u8 = 0;
    let mut v_r_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1894_ = leanh::lean_unbox_usize(v_i_1892_);
    leanh::lean_dec(v_i_1892_);
    v_stop_boxed_1895_ = leanh::lean_unbox_usize(v_stop_1893_);
    leanh::lean_dec(v_stop_1893_);
    v_res_1896_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_1890_, v_as_1891_, v_i_boxed_1894_, v_stop_boxed_1895_);
    leanh::lean_dec_ref(v_as_1891_);
    leanh::lean_dec_ref(v_a_1890_);
    v_r_1897_ = leanh::lean_box((v_res_1896_) as usize);
    return v_r_1897_;
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(
    mut v_as_1898_: *mut leanh::LeanObject,
    mut v_a_1899_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: u8 = 0;
    v___x_1900_ = leanh::lean_unsigned_to_nat(0);
    v___x_1901_ = lean_array_get_size(v_as_1898_);
    v___x_1902_ = lean_nat_dec_lt(v___x_1900_, v___x_1901_);
    if v___x_1902_ == 0 {
        return v___x_1902_;
    } else {
        if v___x_1902_ == 0 {
            return v___x_1902_;
        } else {
            let mut v___x_1903_: usize = 0;
            let mut v___x_1904_: usize = 0;
            let mut v___x_1905_: u8 = 0;
            v___x_1903_ = 0usize;
            v___x_1904_ = lean_usize_of_nat(v___x_1901_);
            v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_1899_, v_as_1898_, v___x_1903_, v___x_1904_);
            return v___x_1905_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2___boxed(
    mut v_as_1906_: *mut leanh::LeanObject,
    mut v_a_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1908_: u8 = 0;
    let mut v_r_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1908_ =
        l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v_as_1906_, v_a_1907_);
    leanh::lean_dec_ref(v_a_1907_);
    leanh::lean_dec_ref(v_as_1906_);
    v_r_1909_ = leanh::lean_box((v_res_1908_) as usize);
    return v_r_1909_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1911_ = l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0;
    v___x_1912_ = l_Lean_stringToMessageData(v___x_1911_);
    return v___x_1912_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(
    mut v_a_1913_: *mut leanh::LeanObject,
    mut v_a_1914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1929_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1913_) == 0 {
                    v___x_1915_ = l_List_reverse___redArg(v_a_1914_);
                    return v___x_1915_;
                } else {
                    v_head_1916_ = leanh::lean_ctor_get(v_a_1913_, 0);
                    v_tail_1917_ = leanh::lean_ctor_get(v_a_1913_, 1);
                    v_isSharedCheck_1929_ = (!leanh::lean_is_exclusive(v_a_1913_)) as u8;
                    if v_isSharedCheck_1929_ == 0 {
                        v___x_1919_ = v_a_1913_;
                        v_isShared_1920_ = v_isSharedCheck_1929_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1917_);
                        leanh::lean_inc(v_head_1916_);
                        leanh::lean_dec(v_a_1913_);
                        v___x_1919_ = leanh::lean_box(0);
                        v_isShared_1920_ = v_isSharedCheck_1929_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1921_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1);
                v___x_1922_ = l_Lean_MessageData_ofExpr(v_head_1916_);
                v___x_1923_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1923_, 0, v___x_1921_);
                leanh::lean_ctor_set(v___x_1923_, 1, v___x_1922_);
                v___x_1924_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1924_, 0, v___x_1923_);
                leanh::lean_ctor_set(v___x_1924_, 1, v___x_1921_);
                if v_isShared_1920_ == 0 {
                    leanh::lean_ctor_set(v___x_1919_, 1, v_a_1914_);
                    leanh::lean_ctor_set(v___x_1919_, 0, v___x_1924_);
                    v___x_1926_ = v___x_1919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1928_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_a_1914_);
                    v___x_1926_ = v_reuseFailAlloc_1928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1913_ = v_tail_1917_;
                v_a_1914_ = v___x_1926_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1933_ = l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2;
    v___x_1934_ = leanh::lean_unsigned_to_nat(14);
    v___x_1935_ = leanh::lean_unsigned_to_nat(22);
    v___x_1936_ = l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1;
    v___x_1937_ = l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0;
    v___x_1938_ = l_mkPanicMessageWithDecl(
        v___x_1937_,
        v___x_1936_,
        v___x_1935_,
        v___x_1934_,
        v___x_1933_,
    );
    return v___x_1938_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1940_ = l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4;
    v___x_1941_ = l_Lean_stringToMessageData(v___x_1940_);
    return v___x_1941_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1943_ = l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6;
    v___x_1944_ = l_Lean_stringToMessageData(v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8;
    v___x_1947_ = l_Lean_stringToMessageData(v___x_1946_);
    return v___x_1947_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10;
    v___x_1950_ = l_Lean_stringToMessageData(v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12;
    v___x_1953_ = l_Lean_stringToMessageData(v___x_1952_);
    return v___x_1953_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_elab___lam__1(
    mut v_body_1954_: *mut leanh::LeanObject,
    mut v_ys_1955_: *mut leanh::LeanObject,
    mut v_vars_1956_: *mut leanh::LeanObject,
    mut v_extraParams_1957_: *mut leanh::LeanObject,
    mut v_structural_1958_: u8,
    mut v_ref_1959_: *mut leanh::LeanObject,
    mut v_xs_1960_: *mut leanh::LeanObject,
    mut v_type_x27_1961_: *mut leanh::LeanObject,
    mut v___y_1962_: *mut leanh::LeanObject,
    mut v___y_1963_: *mut leanh::LeanObject,
    mut v___y_1964_: *mut leanh::LeanObject,
    mut v___y_1965_: *mut leanh::LeanObject,
    mut v___y_1966_: *mut leanh::LeanObject,
    mut v___y_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: u8 = 0;
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: u8 = 0;
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut v_isSharedCheck_2034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1969_ = leanh::lean_box(0);
                v___x_1970_ = 1;
                v___x_1971_ = leanh::lean_box((v___x_1970_) as usize);
                v___x_1972_ = leanh::lean_box((v___x_1970_) as usize);
                v___x_1973_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                leanh::lean_closure_set(v___x_1973_, 0, v_body_1954_);
                leanh::lean_closure_set(v___x_1973_, 1, v___x_1969_);
                leanh::lean_closure_set(v___x_1973_, 2, v___x_1971_);
                leanh::lean_closure_set(v___x_1973_, 3, v___x_1972_);
                leanh::lean_closure_set(v___x_1973_, 4, v___x_1969_);
                v___x_1974_ = 1;
                v___x_1975_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        leanh::lean_box(0),
                        v___x_1973_,
                        v___x_1974_,
                        v___y_1962_,
                        v___y_1963_,
                        v___y_1964_,
                        v___y_1965_,
                        v___y_1966_,
                        v___y_1967_,
                    );
                if leanh::lean_obj_tag(v___x_1975_) == 0 {
                    v_a_1976_ = leanh::lean_ctor_get(v___x_1975_, 0);
                    v_isSharedCheck_2034_ = (!leanh::lean_is_exclusive(v___x_1975_)) as u8;
                    if v_isSharedCheck_2034_ == 0 {
                        v___x_1978_ = v___x_1975_;
                        v_isShared_1979_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1976_);
                        leanh::lean_dec(v___x_1975_);
                        v___x_1978_ = leanh::lean_box(0);
                        v_isShared_1979_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_type_x27_1961_);
                    leanh::lean_dec_ref(v_xs_1960_);
                    leanh::lean_dec_ref(v_ys_1955_);
                    return v___x_1975_;
                }
            }
            1 => {
                v___x_1980_ = leanh::lean_box((v___x_1970_) as usize);
                leanh::lean_inc(v_a_1976_);
                leanh::lean_inc_ref(v_xs_1960_);
                leanh::lean_inc_ref(v_ys_1955_);
                v___f_1981_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_TerminationMeasure_elab___lam__0___boxed as *mut core::ffi::c_void,
                    13,
                    4,
                );
                leanh::lean_closure_set(v___f_1981_, 0, v_ys_1955_);
                leanh::lean_closure_set(v___f_1981_, 1, v_xs_1960_);
                leanh::lean_closure_set(v___f_1981_, 2, v_a_1976_);
                leanh::lean_closure_set(v___f_1981_, 3, v___x_1980_);
                if v_structural_1958_ == 0 {
                    leanh::lean_dec(v_a_1976_);
                    leanh::lean_dec_ref(v_xs_1960_);
                    leanh::lean_dec_ref(v_ys_1955_);
                    v___y_1998_ = v___y_1962_;
                    v___y_1999_ = v___y_1963_;
                    v___y_2000_ = v___y_1964_;
                    v___y_2001_ = v___y_1965_;
                    v___y_2002_ = v___y_1966_;
                    v___y_2003_ = v___y_1967_;
                    state = 4;
                    continue;
                } else {
                    v___x_2007_ = l_Array_append___redArg(v_ys_1955_, v_xs_1960_);
                    leanh::lean_dec_ref(v_xs_1960_);
                    v___x_2008_ =
                        l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(
                            v___x_2007_,
                            v_a_1976_,
                        );
                    if v___x_2008_ == 0 {
                        leanh::lean_dec_ref(v___f_1981_);
                        leanh::lean_del_object(v___x_1978_);
                        leanh::lean_dec(v_type_x27_1961_);
                        v___x_2009_ = lean_array_to_list(v___x_2007_);
                        v___x_2010_ = leanh::lean_box(0);
                        v___x_2011_ =
                            l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(
                                v___x_2009_,
                                v___x_2010_,
                            );
                        v___x_2012_ = l_Lean_MessageData_andList(v___x_2011_);
                        v___x_2013_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5_once
                            ),
                            _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5,
                        );
                        v___x_2014_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7_once
                            ),
                            _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7,
                        );
                        v___x_2015_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2015_, 0, v___x_2014_);
                        leanh::lean_ctor_set(v___x_2015_, 1, v___x_2012_);
                        v___x_2016_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9_once
                            ),
                            _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9,
                        );
                        v___x_2017_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2017_, 0, v___x_2015_);
                        leanh::lean_ctor_set(v___x_2017_, 1, v___x_2016_);
                        v___x_2018_ = l_Lean_indentExpr(v_a_1976_);
                        v___x_2019_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2019_, 0, v___x_2017_);
                        leanh::lean_ctor_set(v___x_2019_, 1, v___x_2018_);
                        v___x_2020_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11_once
                            ),
                            _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11,
                        );
                        v___x_2021_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2021_, 0, v___x_2019_);
                        leanh::lean_ctor_set(v___x_2021_, 1, v___x_2020_);
                        v___x_2022_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2022_, 0, v___x_2013_);
                        leanh::lean_ctor_set(v___x_2022_, 1, v___x_2021_);
                        v___x_2023_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13_once
                            ),
                            _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13,
                        );
                        v___x_2024_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2024_, 0, v___x_2022_);
                        leanh::lean_ctor_set(v___x_2024_, 1, v___x_2023_);
                        v___x_2025_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_1959_, v___x_2024_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
                        v_a_2026_ = leanh::lean_ctor_get(v___x_2025_, 0);
                        v_isSharedCheck_2033_ =
                            (!leanh::lean_is_exclusive(v___x_2025_)) as u8;
                        if v_isSharedCheck_2033_ == 0 {
                            v___x_2028_ = v___x_2025_;
                            v_isShared_2029_ = v_isSharedCheck_2033_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2026_);
                            leanh::lean_dec(v___x_2025_);
                            v___x_2028_ = leanh::lean_box(0);
                            v_isShared_2029_ = v_isSharedCheck_2033_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2007_);
                        leanh::lean_dec(v_a_1976_);
                        v___y_1998_ = v___y_1962_;
                        v___y_1999_ = v___y_1963_;
                        v___y_2000_ = v___y_1964_;
                        v___y_2001_ = v___y_1965_;
                        v___y_2002_ = v___y_1966_;
                        v___y_2003_ = v___y_1967_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1990_ = lean_array_get_size(v_vars_1956_);
                v___x_1991_ = lean_nat_sub(v_extraParams_1957_, v___x_1990_);
                if v_isShared_1979_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1978_, 1);
                    leanh::lean_ctor_set(v___x_1978_, 0, v___x_1991_);
                    v___x_1993_ = v___x_1978_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1996_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1991_);
                    v___x_1993_ = v_reuseFailAlloc_1996_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1994_ = 0;
                v___x_1995_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v___y_1989_, v___x_1993_, v___f_1981_, v___x_1994_, v___x_1994_, v___y_1988_, v___y_1983_, v___y_1984_, v___y_1987_, v___y_1986_, v___y_1985_);
                return v___x_1995_;
            }
            4 => {
                if leanh::lean_obj_tag(v_type_x27_1961_) == 0 {
                    v___x_2004_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3_once
                        ),
                        _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3,
                    );
                    v___x_2005_ =
                        l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__1(v___x_2004_);
                    v___y_1983_ = v___y_1999_;
                    v___y_1984_ = v___y_2000_;
                    v___y_1985_ = v___y_2003_;
                    v___y_1986_ = v___y_2002_;
                    v___y_1987_ = v___y_2001_;
                    v___y_1988_ = v___y_1998_;
                    v___y_1989_ = v___x_2005_;
                    state = 2;
                    continue;
                } else {
                    v_val_2006_ = leanh::lean_ctor_get(v_type_x27_1961_, 0);
                    leanh::lean_inc(v_val_2006_);
                    leanh::lean_dec_ref_known(v_type_x27_1961_, 1);
                    v___y_1983_ = v___y_1999_;
                    v___y_1984_ = v___y_2000_;
                    v___y_1985_ = v___y_2003_;
                    v___y_1986_ = v___y_2002_;
                    v___y_1987_ = v___y_2001_;
                    v___y_1988_ = v___y_1998_;
                    v___y_1989_ = v_val_2006_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2029_ == 0 {
                    v___x_2031_ = v___x_2028_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2032_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
                    v___x_2031_ = v_reuseFailAlloc_2032_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed(
    mut v_body_2035_: *mut leanh::LeanObject,
    mut v_ys_2036_: *mut leanh::LeanObject,
    mut v_vars_2037_: *mut leanh::LeanObject,
    mut v_extraParams_2038_: *mut leanh::LeanObject,
    mut v_structural_2039_: *mut leanh::LeanObject,
    mut v_ref_2040_: *mut leanh::LeanObject,
    mut v_xs_2041_: *mut leanh::LeanObject,
    mut v_type_x27_2042_: *mut leanh::LeanObject,
    mut v___y_2043_: *mut leanh::LeanObject,
    mut v___y_2044_: *mut leanh::LeanObject,
    mut v___y_2045_: *mut leanh::LeanObject,
    mut v___y_2046_: *mut leanh::LeanObject,
    mut v___y_2047_: *mut leanh::LeanObject,
    mut v___y_2048_: *mut leanh::LeanObject,
    mut v___y_2049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structural_boxed_2050_: u8 = 0;
    let mut v_res_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_structural_boxed_2050_ = (leanh::lean_unbox(v_structural_2039_) as u8);
    v_res_2051_ = l_Lean_Elab_TerminationMeasure_elab___lam__1(
        v_body_2035_,
        v_ys_2036_,
        v_vars_2037_,
        v_extraParams_2038_,
        v_structural_boxed_2050_,
        v_ref_2040_,
        v_xs_2041_,
        v_type_x27_2042_,
        v___y_2043_,
        v___y_2044_,
        v___y_2045_,
        v___y_2046_,
        v___y_2047_,
        v___y_2048_,
    );
    leanh::lean_dec(v___y_2048_);
    leanh::lean_dec_ref(v___y_2047_);
    leanh::lean_dec(v___y_2046_);
    leanh::lean_dec_ref(v___y_2045_);
    leanh::lean_dec(v___y_2044_);
    leanh::lean_dec_ref(v___y_2043_);
    leanh::lean_dec(v_ref_2040_);
    leanh::lean_dec(v_extraParams_2038_);
    leanh::lean_dec_ref(v_vars_2037_);
    return v_res_2051_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_elab___lam__2(
    mut v_hint_2052_: *mut leanh::LeanObject,
    mut v_extraParams_2053_: *mut leanh::LeanObject,
    mut v_ys_2054_: *mut leanh::LeanObject,
    mut v_type_x27_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
    mut v___y_2058_: *mut leanh::LeanObject,
    mut v___y_2059_: *mut leanh::LeanObject,
    mut v___y_2060_: *mut leanh::LeanObject,
    mut v___y_2061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_structural_2064_: u8 = 0;
    let mut v_vars_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2063_ = leanh::lean_ctor_get(v_hint_2052_, 0);
    leanh::lean_inc(v_ref_2063_);
    v_structural_2064_ = leanh::lean_ctor_get_uint8(
        v_hint_2052_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v_vars_2065_ = leanh::lean_ctor_get(v_hint_2052_, 1);
    leanh::lean_inc_ref_n(v_vars_2065_, 2);
    v_body_2066_ = leanh::lean_ctor_get(v_hint_2052_, 2);
    leanh::lean_inc(v_body_2066_);
    leanh::lean_dec_ref(v_hint_2052_);
    v___x_2067_ = leanh::lean_box((v_structural_2064_) as usize);
    v___f_2068_ = leanh::lean_alloc_closure(
        l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed as *mut core::ffi::c_void,
        15,
        6,
    );
    leanh::lean_closure_set(v___f_2068_, 0, v_body_2066_);
    leanh::lean_closure_set(v___f_2068_, 1, v_ys_2054_);
    leanh::lean_closure_set(v___f_2068_, 2, v_vars_2065_);
    leanh::lean_closure_set(v___f_2068_, 3, v_extraParams_2053_);
    leanh::lean_closure_set(v___f_2068_, 4, v___x_2067_);
    leanh::lean_closure_set(v___f_2068_, 5, v_ref_2063_);
    v___x_2069_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2069_, 0, v_type_x27_2055_);
    v___x_2070_ = l_Lean_Elab_Term_elabFunBinders___redArg(
        v_vars_2065_,
        v___x_2069_,
        v___f_2068_,
        v___y_2056_,
        v___y_2057_,
        v___y_2058_,
        v___y_2059_,
        v___y_2060_,
        v___y_2061_,
    );
    leanh::lean_dec_ref(v_vars_2065_);
    return v___x_2070_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed(
    mut v_hint_2071_: *mut leanh::LeanObject,
    mut v_extraParams_2072_: *mut leanh::LeanObject,
    mut v_ys_2073_: *mut leanh::LeanObject,
    mut v_type_x27_2074_: *mut leanh::LeanObject,
    mut v___y_2075_: *mut leanh::LeanObject,
    mut v___y_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2082_ = l_Lean_Elab_TerminationMeasure_elab___lam__2(
        v_hint_2071_,
        v_extraParams_2072_,
        v_ys_2073_,
        v_type_x27_2074_,
        v___y_2075_,
        v___y_2076_,
        v___y_2077_,
        v___y_2078_,
        v___y_2079_,
        v___y_2080_,
    );
    leanh::lean_dec(v___y_2080_);
    leanh::lean_dec_ref(v___y_2079_);
    leanh::lean_dec(v___y_2078_);
    leanh::lean_dec_ref(v___y_2077_);
    leanh::lean_dec(v___y_2076_);
    leanh::lean_dec_ref(v___y_2075_);
    return v_res_2082_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2086_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2;
    v___x_2087_ = leanh::lean_unsigned_to_nat(2);
    v___x_2088_ = leanh::lean_unsigned_to_nat(54);
    v___x_2089_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1;
    v___x_2090_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0;
    v___x_2091_ = l_mkPanicMessageWithDecl(
        v___x_2090_,
        v___x_2089_,
        v___x_2088_,
        v___x_2087_,
        v___x_2086_,
    );
    return v___x_2091_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2093_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4;
    v___x_2094_ = l_Lean_stringToMessageData(v___x_2093_);
    return v___x_2094_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6;
    v___x_2097_ = l_Lean_stringToMessageData(v___x_2096_);
    return v___x_2097_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2099_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8;
    v___x_2100_ = l_Lean_stringToMessageData(v___x_2099_);
    return v___x_2100_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2105_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12;
    v___x_2106_ = l_Lean_stringToMessageData(v___x_2105_);
    return v___x_2106_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2110_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15;
    v___x_2111_ = l_Lean_MessageData_ofFormat(v___x_2110_);
    return v___x_2111_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_elab___lam__3(
    mut v___x_2112_: u8,
    mut v_hint_2113_: *mut leanh::LeanObject,
    mut v_arity_2114_: *mut leanh::LeanObject,
    mut v_extraParams_2115_: *mut leanh::LeanObject,
    mut v_type_2116_: *mut leanh::LeanObject,
    mut v___f_2117_: *mut leanh::LeanObject,
    mut v_funName_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
    mut v___y_2120_: *mut leanh::LeanObject,
    mut v___y_2121_: *mut leanh::LeanObject,
    mut v___y_2122_: *mut leanh::LeanObject,
    mut v___y_2123_: *mut leanh::LeanObject,
    mut v___y_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_structural_2129_: u8 = 0;
    let mut v_vars_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: u8 = 0;
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: u8 = 0;
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2150_: u8 = 0;
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut v_unused_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2160_: u8 = 0;
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut v_a_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2172_: u8 = 0;
    let mut v_msg_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2185_: u8 = 0;
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2189_: u8 = 0;
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ident_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_2112_ == 0 {
                    leanh::lean_dec(v_funName_2118_);
                    leanh::lean_dec_ref(v___f_2117_);
                    leanh::lean_dec_ref(v_type_2116_);
                    leanh::lean_dec(v_extraParams_2115_);
                    v___x_2126_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3_once
                        ),
                        _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3,
                    );
                    v___x_2127_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(
                        v___x_2126_,
                        v___y_2119_,
                        v___y_2120_,
                        v___y_2121_,
                        v___y_2122_,
                        v___y_2123_,
                        v___y_2124_,
                    );
                    return v___x_2127_;
                } else {
                    v_ref_2128_ = leanh::lean_ctor_get(v_hint_2113_, 0);
                    v_structural_2129_ = leanh::lean_ctor_get_uint8(
                        v_hint_2113_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_vars_2130_ = leanh::lean_ctor_get(v_hint_2113_, 1);
                    v___x_2190_ = lean_array_get_size(v_vars_2130_);
                    v___x_2191_ = lean_nat_dec_lt(v_extraParams_2115_, v___x_2190_);
                    if v___x_2191_ == 0 {
                        leanh::lean_dec(v_funName_2118_);
                        v___y_2132_ = v___y_2119_;
                        v___y_2133_ = v___y_2120_;
                        v___y_2134_ = v___y_2121_;
                        v___y_2135_ = v___y_2122_;
                        v___y_2136_ = v___y_2123_;
                        v___y_2137_ = v___y_2124_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___f_2117_);
                        leanh::lean_dec_ref(v_type_2116_);
                        v___x_2192_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v___x_2190_);
                        v___x_2193_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5_once
                            ),
                            _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5,
                        );
                        v___x_2194_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2194_, 0, v___x_2192_);
                        leanh::lean_ctor_set(v___x_2194_, 1, v___x_2193_);
                        leanh::lean_inc(v_funName_2118_);
                        v___x_2195_ = l_Lean_MessageData_ofName(v_funName_2118_);
                        v___x_2196_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7_once
                            ),
                            _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7,
                        );
                        v___x_2197_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2197_, 0, v___x_2195_);
                        leanh::lean_ctor_set(v___x_2197_, 1, v___x_2196_);
                        v___x_2198_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v_extraParams_2115_);
                        v___x_2199_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2199_, 0, v___x_2197_);
                        leanh::lean_ctor_set(v___x_2199_, 1, v___x_2198_);
                        v___x_2200_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9_once
                            ),
                            _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9,
                        );
                        v___x_2201_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2201_, 0, v___x_2199_);
                        leanh::lean_ctor_set(v___x_2201_, 1, v___x_2200_);
                        v_msg_2202_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_msg_2202_, 0, v___x_2194_);
                        leanh::lean_ctor_set(v_msg_2202_, 1, v___x_2201_);
                        v___x_2203_ = leanh::lean_unsigned_to_nat(0);
                        v_ident_2204_ = lean_array_fget_borrowed(v_vars_2130_, v___x_2203_);
                        v___x_2205_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11;
                        leanh::lean_inc(v_ident_2204_);
                        v___x_2206_ = l_Lean_Syntax_isOfKind(v_ident_2204_, v___x_2205_);
                        if v___x_2206_ == 0 {
                            leanh::lean_dec(v_funName_2118_);
                            v_msg_2174_ = v_msg_2202_;
                            v___y_2175_ = v___y_2119_;
                            v___y_2176_ = v___y_2120_;
                            v___y_2177_ = v___y_2121_;
                            v___y_2178_ = v___y_2122_;
                            v___y_2179_ = v___y_2123_;
                            v___y_2180_ = v___y_2124_;
                            state = 8;
                            continue;
                        } else {
                            v___x_2207_ = l_Lean_TSyntax_getId(v_ident_2204_);
                            v___x_2208_ = l_Lean_Name_isSuffixOf(v___x_2207_, v_funName_2118_);
                            leanh::lean_dec(v_funName_2118_);
                            leanh::lean_dec(v___x_2207_);
                            if v___x_2208_ == 0 {
                                v_msg_2174_ = v_msg_2202_;
                                v___y_2175_ = v___y_2119_;
                                v___y_2176_ = v___y_2120_;
                                v___y_2177_ = v___y_2121_;
                                v___y_2178_ = v___y_2122_;
                                v___y_2179_ = v___y_2123_;
                                v___y_2180_ = v___y_2124_;
                                state = 8;
                                continue;
                            } else {
                                v___x_2209_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13_once), _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13);
                                v___x_2210_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2210_, 0, v_msg_2202_);
                                leanh::lean_ctor_set(v___x_2210_, 1, v___x_2209_);
                                v___x_2211_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16), core::ptr::addr_of_mut!(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16_once), _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16);
                                v_msg_2212_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v_msg_2212_, 0, v___x_2210_);
                                leanh::lean_ctor_set(v_msg_2212_, 1, v___x_2211_);
                                v_msg_2174_ = v_msg_2212_;
                                v___y_2175_ = v___y_2119_;
                                v___y_2176_ = v___y_2120_;
                                v___y_2177_ = v___y_2121_;
                                v___y_2178_ = v___y_2122_;
                                v___y_2179_ = v___y_2123_;
                                v___y_2180_ = v___y_2124_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2138_ = lean_nat_sub(v_arity_2114_, v_extraParams_2115_);
                leanh::lean_dec(v_extraParams_2115_);
                v___x_2139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2139_, 0, v___x_2138_);
                v___x_2140_ = 0;
                v___x_2141_ = leanh::lean_box((v___x_2112_) as usize);
                v___x_2142_ = leanh::lean_box((v___x_2140_) as usize);
                v___x_2143_ = leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___boxed as *mut core::ffi::c_void, 13, 6);
                leanh::lean_closure_set(v___x_2143_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2143_, 1, v_type_2116_);
                leanh::lean_closure_set(v___x_2143_, 2, v___x_2139_);
                leanh::lean_closure_set(v___x_2143_, 3, v___f_2117_);
                leanh::lean_closure_set(v___x_2143_, 4, v___x_2141_);
                leanh::lean_closure_set(v___x_2143_, 5, v___x_2142_);
                v___x_2144_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
                    v___x_2143_,
                    v___y_2132_,
                    v___y_2133_,
                    v___y_2134_,
                    v___y_2135_,
                    v___y_2136_,
                    v___y_2137_,
                );
                if leanh::lean_obj_tag(v___x_2144_) == 0 {
                    v_a_2145_ = leanh::lean_ctor_get(v___x_2144_, 0);
                    leanh::lean_inc_n(v_a_2145_, 2);
                    leanh::lean_dec_ref_known(v___x_2144_, 1);
                    v___x_2146_ = 0;
                    v___x_2147_ = l_Lean_Meta_check(
                        v_a_2145_,
                        v___x_2146_,
                        v___y_2134_,
                        v___y_2135_,
                        v___y_2136_,
                        v___y_2137_,
                    );
                    if leanh::lean_obj_tag(v___x_2147_) == 0 {
                        v_isSharedCheck_2155_ =
                            (!leanh::lean_is_exclusive(v___x_2147_)) as u8;
                        if v_isSharedCheck_2155_ == 0 {
                            v_unused_2156_ = leanh::lean_ctor_get(v___x_2147_, 0);
                            leanh::lean_dec(v_unused_2156_);
                            v___x_2149_ = v___x_2147_;
                            v_isShared_2150_ = v_isSharedCheck_2155_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2147_);
                            v___x_2149_ = leanh::lean_box(0);
                            v_isShared_2150_ = v_isSharedCheck_2155_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2145_);
                        v_a_2157_ = leanh::lean_ctor_get(v___x_2147_, 0);
                        v_isSharedCheck_2164_ =
                            (!leanh::lean_is_exclusive(v___x_2147_)) as u8;
                        if v_isSharedCheck_2164_ == 0 {
                            v___x_2159_ = v___x_2147_;
                            v_isShared_2160_ = v_isSharedCheck_2164_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2157_);
                            leanh::lean_dec(v___x_2147_);
                            v___x_2159_ = leanh::lean_box(0);
                            v_isShared_2160_ = v_isSharedCheck_2164_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_2165_ = leanh::lean_ctor_get(v___x_2144_, 0);
                    v_isSharedCheck_2172_ = (!leanh::lean_is_exclusive(v___x_2144_)) as u8;
                    if v_isSharedCheck_2172_ == 0 {
                        v___x_2167_ = v___x_2144_;
                        v_isShared_2168_ = v_isSharedCheck_2172_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2165_);
                        leanh::lean_dec(v___x_2144_);
                        v___x_2167_ = leanh::lean_box(0);
                        v_isShared_2168_ = v_isSharedCheck_2172_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_ref_2128_);
                v___x_2151_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_2151_, 0, v_ref_2128_);
                leanh::lean_ctor_set(v___x_2151_, 1, v_a_2145_);
                leanh::lean_ctor_set_uint8(
                    v___x_2151_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_structural_2129_,
                );
                if v_isShared_2150_ == 0 {
                    leanh::lean_ctor_set(v___x_2149_, 0, v___x_2151_);
                    v___x_2153_ = v___x_2149_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
                    v___x_2153_ = v_reuseFailAlloc_2154_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2153_;
            }
            4 => {
                if v_isShared_2160_ == 0 {
                    v___x_2162_ = v___x_2159_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
                    v___x_2162_ = v_reuseFailAlloc_2163_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2162_;
            }
            6 => {
                if v_isShared_2168_ == 0 {
                    v___x_2170_ = v___x_2167_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
                    v___x_2170_ = v_reuseFailAlloc_2171_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2170_;
            }
            8 => {
                v___x_2181_ =
                    l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(
                        v_ref_2128_,
                        v_msg_2174_,
                        v___y_2175_,
                        v___y_2176_,
                        v___y_2177_,
                        v___y_2178_,
                        v___y_2179_,
                        v___y_2180_,
                    );
                v_a_2182_ = leanh::lean_ctor_get(v___x_2181_, 0);
                v_isSharedCheck_2189_ = (!leanh::lean_is_exclusive(v___x_2181_)) as u8;
                if v_isSharedCheck_2189_ == 0 {
                    v___x_2184_ = v___x_2181_;
                    v_isShared_2185_ = v_isSharedCheck_2189_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2182_);
                    leanh::lean_dec(v___x_2181_);
                    v___x_2184_ = leanh::lean_box(0);
                    v_isShared_2185_ = v_isSharedCheck_2189_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2185_ == 0 {
                    v___x_2187_ = v___x_2184_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2188_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
                    v___x_2187_ = v_reuseFailAlloc_2188_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed(
    mut v___x_2213_: *mut leanh::LeanObject,
    mut v_hint_2214_: *mut leanh::LeanObject,
    mut v_arity_2215_: *mut leanh::LeanObject,
    mut v_extraParams_2216_: *mut leanh::LeanObject,
    mut v_type_2217_: *mut leanh::LeanObject,
    mut v___f_2218_: *mut leanh::LeanObject,
    mut v_funName_2219_: *mut leanh::LeanObject,
    mut v___y_2220_: *mut leanh::LeanObject,
    mut v___y_2221_: *mut leanh::LeanObject,
    mut v___y_2222_: *mut leanh::LeanObject,
    mut v___y_2223_: *mut leanh::LeanObject,
    mut v___y_2224_: *mut leanh::LeanObject,
    mut v___y_2225_: *mut leanh::LeanObject,
    mut v___y_2226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6766__boxed_2227_: u8 = 0;
    let mut v_res_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6766__boxed_2227_ = (leanh::lean_unbox(v___x_2213_) as u8);
    v_res_2228_ = l_Lean_Elab_TerminationMeasure_elab___lam__3(
        v___x_6766__boxed_2227_,
        v_hint_2214_,
        v_arity_2215_,
        v_extraParams_2216_,
        v_type_2217_,
        v___f_2218_,
        v_funName_2219_,
        v___y_2220_,
        v___y_2221_,
        v___y_2222_,
        v___y_2223_,
        v___y_2224_,
        v___y_2225_,
    );
    leanh::lean_dec(v___y_2225_);
    leanh::lean_dec_ref(v___y_2224_);
    leanh::lean_dec(v___y_2223_);
    leanh::lean_dec_ref(v___y_2222_);
    leanh::lean_dec(v___y_2221_);
    leanh::lean_dec_ref(v___y_2220_);
    leanh::lean_dec(v_arity_2215_);
    leanh::lean_dec_ref(v_hint_2214_);
    return v_res_2228_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_elab(
    mut v_funName_2229_: *mut leanh::LeanObject,
    mut v_type_2230_: *mut leanh::LeanObject,
    mut v_arity_2231_: *mut leanh::LeanObject,
    mut v_extraParams_2232_: *mut leanh::LeanObject,
    mut v_hint_2233_: *mut leanh::LeanObject,
    mut v_a_2234_: *mut leanh::LeanObject,
    mut v_a_2235_: *mut leanh::LeanObject,
    mut v_a_2236_: *mut leanh::LeanObject,
    mut v_a_2237_: *mut leanh::LeanObject,
    mut v_a_2238_: *mut leanh::LeanObject,
    mut v_a_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_extraParams_2232_);
    leanh::lean_inc_ref(v_hint_2233_);
    v___f_2241_ = leanh::lean_alloc_closure(
        l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    leanh::lean_closure_set(v___f_2241_, 0, v_hint_2233_);
    leanh::lean_closure_set(v___f_2241_, 1, v_extraParams_2232_);
    v___x_2242_ = lean_nat_dec_le(v_extraParams_2232_, v_arity_2231_);
    v___x_2243_ = leanh::lean_box((v___x_2242_) as usize);
    leanh::lean_inc(v_funName_2229_);
    v___y_2244_ = leanh::lean_alloc_closure(
        l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed as *mut core::ffi::c_void,
        14,
        7,
    );
    leanh::lean_closure_set(v___y_2244_, 0, v___x_2243_);
    leanh::lean_closure_set(v___y_2244_, 1, v_hint_2233_);
    leanh::lean_closure_set(v___y_2244_, 2, v_arity_2231_);
    leanh::lean_closure_set(v___y_2244_, 3, v_extraParams_2232_);
    leanh::lean_closure_set(v___y_2244_, 4, v_type_2230_);
    leanh::lean_closure_set(v___y_2244_, 5, v___f_2241_);
    leanh::lean_closure_set(v___y_2244_, 6, v_funName_2229_);
    v___x_2245_ = l_Lean_Elab_Term_withDeclName___redArg(
        v_funName_2229_,
        v___y_2244_,
        v_a_2234_,
        v_a_2235_,
        v_a_2236_,
        v_a_2237_,
        v_a_2238_,
        v_a_2239_,
    );
    return v___x_2245_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_elab___boxed(
    mut v_funName_2246_: *mut leanh::LeanObject,
    mut v_type_2247_: *mut leanh::LeanObject,
    mut v_arity_2248_: *mut leanh::LeanObject,
    mut v_extraParams_2249_: *mut leanh::LeanObject,
    mut v_hint_2250_: *mut leanh::LeanObject,
    mut v_a_2251_: *mut leanh::LeanObject,
    mut v_a_2252_: *mut leanh::LeanObject,
    mut v_a_2253_: *mut leanh::LeanObject,
    mut v_a_2254_: *mut leanh::LeanObject,
    mut v_a_2255_: *mut leanh::LeanObject,
    mut v_a_2256_: *mut leanh::LeanObject,
    mut v_a_2257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2258_ = l_Lean_Elab_TerminationMeasure_elab(
        v_funName_2246_,
        v_type_2247_,
        v_arity_2248_,
        v_extraParams_2249_,
        v_hint_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
        v_a_2254_,
        v_a_2255_,
        v_a_2256_,
    );
    leanh::lean_dec(v_a_2256_);
    leanh::lean_dec_ref(v_a_2255_);
    leanh::lean_dec(v_a_2254_);
    leanh::lean_dec_ref(v_a_2253_);
    leanh::lean_dec(v_a_2252_);
    leanh::lean_dec_ref(v_a_2251_);
    return v_res_2258_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(
    mut v_00_u03b1_2259_: *mut leanh::LeanObject,
    mut v_ref_2260_: *mut leanh::LeanObject,
    mut v_msg_2261_: *mut leanh::LeanObject,
    mut v___y_2262_: *mut leanh::LeanObject,
    mut v___y_2263_: *mut leanh::LeanObject,
    mut v___y_2264_: *mut leanh::LeanObject,
    mut v___y_2265_: *mut leanh::LeanObject,
    mut v___y_2266_: *mut leanh::LeanObject,
    mut v___y_2267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2269_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(
        v_ref_2260_,
        v_msg_2261_,
        v___y_2262_,
        v___y_2263_,
        v___y_2264_,
        v___y_2265_,
        v___y_2266_,
        v___y_2267_,
    );
    return v___x_2269_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___boxed(
    mut v_00_u03b1_2270_: *mut leanh::LeanObject,
    mut v_ref_2271_: *mut leanh::LeanObject,
    mut v_msg_2272_: *mut leanh::LeanObject,
    mut v___y_2273_: *mut leanh::LeanObject,
    mut v___y_2274_: *mut leanh::LeanObject,
    mut v___y_2275_: *mut leanh::LeanObject,
    mut v___y_2276_: *mut leanh::LeanObject,
    mut v___y_2277_: *mut leanh::LeanObject,
    mut v___y_2278_: *mut leanh::LeanObject,
    mut v___y_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2280_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(
        v_00_u03b1_2270_,
        v_ref_2271_,
        v_msg_2272_,
        v___y_2273_,
        v___y_2274_,
        v___y_2275_,
        v___y_2276_,
        v___y_2277_,
        v___y_2278_,
    );
    leanh::lean_dec(v___y_2278_);
    leanh::lean_dec_ref(v___y_2277_);
    leanh::lean_dec(v___y_2276_);
    leanh::lean_dec_ref(v___y_2275_);
    leanh::lean_dec(v___y_2274_);
    leanh::lean_dec_ref(v___y_2273_);
    leanh::lean_dec(v_ref_2271_);
    return v_res_2280_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(
    mut v_00_u03b1_2281_: *mut leanh::LeanObject,
    mut v_msg_2282_: *mut leanh::LeanObject,
    mut v___y_2283_: *mut leanh::LeanObject,
    mut v___y_2284_: *mut leanh::LeanObject,
    mut v___y_2285_: *mut leanh::LeanObject,
    mut v___y_2286_: *mut leanh::LeanObject,
    mut v___y_2287_: *mut leanh::LeanObject,
    mut v___y_2288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2290_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
    return v___x_2290_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___boxed(
    mut v_00_u03b1_2291_: *mut leanh::LeanObject,
    mut v_msg_2292_: *mut leanh::LeanObject,
    mut v___y_2293_: *mut leanh::LeanObject,
    mut v___y_2294_: *mut leanh::LeanObject,
    mut v___y_2295_: *mut leanh::LeanObject,
    mut v___y_2296_: *mut leanh::LeanObject,
    mut v___y_2297_: *mut leanh::LeanObject,
    mut v___y_2298_: *mut leanh::LeanObject,
    mut v___y_2299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2300_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(v_00_u03b1_2291_, v_msg_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
    leanh::lean_dec(v___y_2298_);
    leanh::lean_dec_ref(v___y_2297_);
    leanh::lean_dec(v___y_2296_);
    leanh::lean_dec_ref(v___y_2295_);
    leanh::lean_dec(v___y_2294_);
    leanh::lean_dec_ref(v___y_2293_);
    return v_res_2300_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(
    mut v_msgData_2301_: *mut leanh::LeanObject,
    mut v_macroStack_2302_: *mut leanh::LeanObject,
    mut v___y_2303_: *mut leanh::LeanObject,
    mut v___y_2304_: *mut leanh::LeanObject,
    mut v___y_2305_: *mut leanh::LeanObject,
    mut v___y_2306_: *mut leanh::LeanObject,
    mut v___y_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_msgData_2301_, v_macroStack_2302_, v___y_2307_);
    return v___x_2310_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___boxed(
    mut v_msgData_2311_: *mut leanh::LeanObject,
    mut v_macroStack_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
    mut v___y_2314_: *mut leanh::LeanObject,
    mut v___y_2315_: *mut leanh::LeanObject,
    mut v___y_2316_: *mut leanh::LeanObject,
    mut v___y_2317_: *mut leanh::LeanObject,
    mut v___y_2318_: *mut leanh::LeanObject,
    mut v___y_2319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(v_msgData_2311_, v_macroStack_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
    leanh::lean_dec(v___y_2318_);
    leanh::lean_dec_ref(v___y_2317_);
    leanh::lean_dec(v___y_2316_);
    leanh::lean_dec_ref(v___y_2315_);
    leanh::lean_dec(v___y_2314_);
    leanh::lean_dec_ref(v___y_2313_);
    return v_res_2320_;
}
pub unsafe fn l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(
    mut v_msg_2322_: *mut leanh::LeanObject,
    mut v___y_2323_: *mut leanh::LeanObject,
    mut v___y_2324_: *mut leanh::LeanObject,
    mut v___y_2325_: *mut leanh::LeanObject,
    mut v___y_2326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417__overap_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2328_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0;
    v___x_417__overap_2329_ = lean_panic_fn_borrowed(v___f_2328_, v_msg_2322_);
    leanh::lean_inc(v___y_2326_);
    leanh::lean_inc_ref(v___y_2325_);
    leanh::lean_inc(v___y_2324_);
    leanh::lean_inc_ref(v___y_2323_);
    v___x_2330_ = leanh::lean_apply_5(
        v___x_417__overap_2329_,
        v___y_2323_,
        v___y_2324_,
        v___y_2325_,
        v___y_2326_,
        leanh::lean_box(0),
    );
    return v___x_2330_;
}
pub unsafe fn l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___boxed(
    mut v_msg_2331_: *mut leanh::LeanObject,
    mut v___y_2332_: *mut leanh::LeanObject,
    mut v___y_2333_: *mut leanh::LeanObject,
    mut v___y_2334_: *mut leanh::LeanObject,
    mut v___y_2335_: *mut leanh::LeanObject,
    mut v___y_2336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2337_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(
        v_msg_2331_,
        v___y_2332_,
        v___y_2333_,
        v___y_2334_,
        v___y_2335_,
    );
    leanh::lean_dec(v___y_2335_);
    leanh::lean_dec_ref(v___y_2334_);
    leanh::lean_dec(v___y_2333_);
    leanh::lean_dec_ref(v___y_2332_);
    return v_res_2337_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(
    mut v_k_2338_: *mut leanh::LeanObject,
    mut v_b_2339_: *mut leanh::LeanObject,
    mut v_c_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2344_);
    leanh::lean_inc_ref(v___y_2343_);
    leanh::lean_inc(v___y_2342_);
    leanh::lean_inc_ref(v___y_2341_);
    v___x_2346_ = leanh::lean_apply_7(
        v_k_2338_,
        v_b_2339_,
        v_c_2340_,
        v___y_2341_,
        v___y_2342_,
        v___y_2343_,
        v___y_2344_,
        leanh::lean_box(0),
    );
    return v___x_2346_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed(
    mut v_k_2347_: *mut leanh::LeanObject,
    mut v_b_2348_: *mut leanh::LeanObject,
    mut v_c_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
    mut v___y_2352_: *mut leanh::LeanObject,
    mut v___y_2353_: *mut leanh::LeanObject,
    mut v___y_2354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2355_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(v_k_2347_, v_b_2348_, v_c_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
    leanh::lean_dec(v___y_2353_);
    leanh::lean_dec_ref(v___y_2352_);
    leanh::lean_dec(v___y_2351_);
    leanh::lean_dec_ref(v___y_2350_);
    return v_res_2355_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(
    mut v_e_2356_: *mut leanh::LeanObject,
    mut v_k_2357_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2358_: u8,
    mut v___y_2359_: *mut leanh::LeanObject,
    mut v___y_2360_: *mut leanh::LeanObject,
    mut v___y_2361_: *mut leanh::LeanObject,
    mut v___y_2362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2372_: u8 = 0;
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut v_a_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2364_ = leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2364_, 0, v_k_2357_);
                v___x_2365_ = 1;
                v___x_2366_ = 0;
                v___x_2367_ = leanh::lean_box(0);
                v___x_2368_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    leanh::lean_box(0),
                    v_e_2356_,
                    v___x_2365_,
                    v___x_2366_,
                    v___x_2365_,
                    v___x_2366_,
                    v___x_2367_,
                    v___f_2364_,
                    v_cleanupAnnotations_2358_,
                    v___y_2359_,
                    v___y_2360_,
                    v___y_2361_,
                    v___y_2362_,
                );
                if leanh::lean_obj_tag(v___x_2368_) == 0 {
                    v_a_2369_ = leanh::lean_ctor_get(v___x_2368_, 0);
                    v_isSharedCheck_2376_ = (!leanh::lean_is_exclusive(v___x_2368_)) as u8;
                    if v_isSharedCheck_2376_ == 0 {
                        v___x_2371_ = v___x_2368_;
                        v_isShared_2372_ = v_isSharedCheck_2376_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2369_);
                        leanh::lean_dec(v___x_2368_);
                        v___x_2371_ = leanh::lean_box(0);
                        v_isShared_2372_ = v_isSharedCheck_2376_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2377_ = leanh::lean_ctor_get(v___x_2368_, 0);
                    v_isSharedCheck_2384_ = (!leanh::lean_is_exclusive(v___x_2368_)) as u8;
                    if v_isSharedCheck_2384_ == 0 {
                        v___x_2379_ = v___x_2368_;
                        v_isShared_2380_ = v_isSharedCheck_2384_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2377_);
                        leanh::lean_dec(v___x_2368_);
                        v___x_2379_ = leanh::lean_box(0);
                        v_isShared_2380_ = v_isSharedCheck_2384_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2372_ == 0 {
                    v___x_2374_ = v___x_2371_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2375_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
                    v___x_2374_ = v_reuseFailAlloc_2375_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2374_;
            }
            3 => {
                if v_isShared_2380_ == 0 {
                    v___x_2382_ = v___x_2379_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
                    v___x_2382_ = v_reuseFailAlloc_2383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___boxed(
    mut v_e_2385_: *mut leanh::LeanObject,
    mut v_k_2386_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2387_: *mut leanh::LeanObject,
    mut v___y_2388_: *mut leanh::LeanObject,
    mut v___y_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
    mut v___y_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2393_: u8 = 0;
    let mut v_res_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2393_ = (leanh::lean_unbox(v_cleanupAnnotations_2387_) as u8);
    v_res_2394_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_2385_, v_k_2386_, v_cleanupAnnotations_boxed_2393_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
    leanh::lean_dec(v___y_2391_);
    leanh::lean_dec_ref(v___y_2390_);
    leanh::lean_dec(v___y_2389_);
    leanh::lean_dec_ref(v___y_2388_);
    return v_res_2394_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(
    mut v_00_u03b1_2395_: *mut leanh::LeanObject,
    mut v_e_2396_: *mut leanh::LeanObject,
    mut v_k_2397_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2398_: u8,
    mut v___y_2399_: *mut leanh::LeanObject,
    mut v___y_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
    mut v___y_2402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2404_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_2396_, v_k_2397_, v_cleanupAnnotations_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
    return v___x_2404_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___boxed(
    mut v_00_u03b1_2405_: *mut leanh::LeanObject,
    mut v_e_2406_: *mut leanh::LeanObject,
    mut v_k_2407_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2408_: *mut leanh::LeanObject,
    mut v___y_2409_: *mut leanh::LeanObject,
    mut v___y_2410_: *mut leanh::LeanObject,
    mut v___y_2411_: *mut leanh::LeanObject,
    mut v___y_2412_: *mut leanh::LeanObject,
    mut v___y_2413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2414_: u8 = 0;
    let mut v_res_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2414_ = (leanh::lean_unbox(v_cleanupAnnotations_2408_) as u8);
    v_res_2415_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(
            v_00_u03b1_2405_,
            v_e_2406_,
            v_k_2407_,
            v_cleanupAnnotations_boxed_2414_,
            v___y_2409_,
            v___y_2410_,
            v___y_2411_,
            v___y_2412_,
        );
    leanh::lean_dec(v___y_2412_);
    leanh::lean_dec_ref(v___y_2411_);
    leanh::lean_dec(v___y_2410_);
    leanh::lean_dec_ref(v___y_2409_);
    return v_res_2415_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(
    mut v_xs_2416_: *mut leanh::LeanObject,
    mut v_v_2417_: *mut leanh::LeanObject,
    mut v_i_2418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: u8 = 0;
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2419_ = lean_array_get_size(v_xs_2416_);
                v___x_2420_ = lean_nat_dec_lt(v_i_2418_, v___x_2419_);
                if v___x_2420_ == 0 {
                    leanh::lean_dec(v_i_2418_);
                    v___x_2421_ = leanh::lean_box(0);
                    return v___x_2421_;
                } else {
                    v___x_2422_ = lean_array_fget_borrowed(v_xs_2416_, v_i_2418_);
                    v___x_2423_ = lean_expr_eqv(v___x_2422_, v_v_2417_);
                    if v___x_2423_ == 0 {
                        v___x_2424_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2425_ = lean_nat_add(v_i_2418_, v___x_2424_);
                        leanh::lean_dec(v_i_2418_);
                        v_i_2418_ = v___x_2425_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2427_, 0, v_i_2418_);
                        return v___x_2427_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3___boxed(
    mut v_xs_2428_: *mut leanh::LeanObject,
    mut v_v_2429_: *mut leanh::LeanObject,
    mut v_i_2430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(v_xs_2428_, v_v_2429_, v_i_2430_);
    leanh::lean_dec_ref(v_v_2429_);
    leanh::lean_dec_ref(v_xs_2428_);
    return v_res_2431_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(
    mut v_xs_2432_: *mut leanh::LeanObject,
    mut v_v_2433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2434_ = leanh::lean_unsigned_to_nat(0);
    v___x_2435_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(v_xs_2432_, v_v_2433_, v___x_2434_);
    return v___x_2435_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0___boxed(
    mut v_xs_2436_: *mut leanh::LeanObject,
    mut v_v_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2438_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(v_xs_2436_, v_v_2437_);
    leanh::lean_dec_ref(v_v_2437_);
    leanh::lean_dec_ref(v_xs_2436_);
    return v_res_2438_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(
    mut v_xs_2439_: *mut leanh::LeanObject,
    mut v_v_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2446_: u8 = 0;
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2441_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(v_xs_2439_, v_v_2440_);
                if leanh::lean_obj_tag(v___x_2441_) == 0 {
                    v___x_2442_ = leanh::lean_box(0);
                    return v___x_2442_;
                } else {
                    v_val_2443_ = leanh::lean_ctor_get(v___x_2441_, 0);
                    v_isSharedCheck_2450_ = (!leanh::lean_is_exclusive(v___x_2441_)) as u8;
                    if v_isSharedCheck_2450_ == 0 {
                        v___x_2445_ = v___x_2441_;
                        v_isShared_2446_ = v_isSharedCheck_2450_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2443_);
                        leanh::lean_dec(v___x_2441_);
                        v___x_2445_ = leanh::lean_box(0);
                        v_isShared_2446_ = v_isSharedCheck_2450_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2446_ == 0 {
                    v___x_2448_ = v___x_2445_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_val_2443_);
                    v___x_2448_ = v_reuseFailAlloc_2449_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0___boxed(
    mut v_xs_2451_: *mut leanh::LeanObject,
    mut v_v_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(
        v_xs_2451_, v_v_2452_,
    );
    leanh::lean_dec_ref(v_v_2452_);
    leanh::lean_dec_ref(v_xs_2451_);
    return v_res_2453_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ = l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1;
    v___x_2457_ = leanh::lean_unsigned_to_nat(8);
    v___x_2458_ = leanh::lean_unsigned_to_nat(93);
    v___x_2459_ = l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0;
    v___x_2460_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0;
    v___x_2461_ = l_mkPanicMessageWithDecl(
        v___x_2460_,
        v___x_2459_,
        v___x_2458_,
        v___x_2457_,
        v___x_2456_,
    );
    return v___x_2461_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(
    mut v_ys_2462_: *mut leanh::LeanObject,
    mut v_e_2463_: *mut leanh::LeanObject,
    mut v___y_2464_: *mut leanh::LeanObject,
    mut v___y_2465_: *mut leanh::LeanObject,
    mut v___y_2466_: *mut leanh::LeanObject,
    mut v___y_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2473_: u8 = 0;
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2477_: u8 = 0;
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2469_ =
                    l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(
                        v_ys_2462_, v_e_2463_,
                    );
                if leanh::lean_obj_tag(v___x_2469_) == 1 {
                    v_val_2470_ = leanh::lean_ctor_get(v___x_2469_, 0);
                    v_isSharedCheck_2477_ = (!leanh::lean_is_exclusive(v___x_2469_)) as u8;
                    if v_isSharedCheck_2477_ == 0 {
                        v___x_2472_ = v___x_2469_;
                        v_isShared_2473_ = v_isSharedCheck_2477_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2470_);
                        leanh::lean_dec(v___x_2469_);
                        v___x_2472_ = leanh::lean_box(0);
                        v_isShared_2473_ = v_isSharedCheck_2477_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2469_);
                    v___x_2478_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2_once
                        ),
                        _init_l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2,
                    );
                    v___x_2479_ =
                        l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(
                            v___x_2478_,
                            v___y_2464_,
                            v___y_2465_,
                            v___y_2466_,
                            v___y_2467_,
                        );
                    return v___x_2479_;
                }
            }
            1 => {
                if v_isShared_2473_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2472_, 0);
                    v___x_2475_ = v___x_2472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2476_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_val_2470_);
                    v___x_2475_ = v_reuseFailAlloc_2476_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___boxed(
    mut v_ys_2480_: *mut leanh::LeanObject,
    mut v_e_2481_: *mut leanh::LeanObject,
    mut v___y_2482_: *mut leanh::LeanObject,
    mut v___y_2483_: *mut leanh::LeanObject,
    mut v___y_2484_: *mut leanh::LeanObject,
    mut v___y_2485_: *mut leanh::LeanObject,
    mut v___y_2486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2487_ = l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(
        v_ys_2480_,
        v_e_2481_,
        v___y_2482_,
        v___y_2483_,
        v___y_2484_,
        v___y_2485_,
    );
    leanh::lean_dec(v___y_2485_);
    leanh::lean_dec_ref(v___y_2484_);
    leanh::lean_dec(v___y_2483_);
    leanh::lean_dec_ref(v___y_2482_);
    leanh::lean_dec_ref(v_e_2481_);
    leanh::lean_dec_ref(v_ys_2480_);
    return v_res_2487_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationMeasure_structuralArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Lean_Elab_TerminationMeasure_structuralArg___closed__0;
    v___x_2490_ = leanh::lean_unsigned_to_nat(2);
    v___x_2491_ = leanh::lean_unsigned_to_nat(90);
    v___x_2492_ = l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0;
    v___x_2493_ = l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0;
    v___x_2494_ = l_mkPanicMessageWithDecl(
        v___x_2493_,
        v___x_2492_,
        v___x_2491_,
        v___x_2490_,
        v___x_2489_,
    );
    return v___x_2494_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_structuralArg(
    mut v_measure_2496_: *mut leanh::LeanObject,
    mut v_a_2497_: *mut leanh::LeanObject,
    mut v_a_2498_: *mut leanh::LeanObject,
    mut v_a_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structural_2502_: u8 = 0;
    v_structural_2502_ = leanh::lean_ctor_get_uint8(
        v_measure_2496_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    if v_structural_2502_ == 0 {
        let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_measure_2496_);
        v___x_2503_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_TerminationMeasure_structuralArg___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Elab_TerminationMeasure_structuralArg___closed__1_once),
            _init_l_Lean_Elab_TerminationMeasure_structuralArg___closed__1,
        );
        v___x_2504_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(
            v___x_2503_,
            v_a_2497_,
            v_a_2498_,
            v_a_2499_,
            v_a_2500_,
        );
        return v___x_2504_;
    } else {
        let mut v_fn_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2507_: u8 = 0;
        let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_fn_2505_ = leanh::lean_ctor_get(v_measure_2496_, 1);
        leanh::lean_inc_ref(v_fn_2505_);
        leanh::lean_dec_ref(v_measure_2496_);
        v___f_2506_ = l_Lean_Elab_TerminationMeasure_structuralArg___closed__2;
        v___x_2507_ = 0;
        v___x_2508_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_fn_2505_, v___f_2506_, v___x_2507_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
        return v___x_2508_;
    }
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_structuralArg___boxed(
    mut v_measure_2509_: *mut leanh::LeanObject,
    mut v_a_2510_: *mut leanh::LeanObject,
    mut v_a_2511_: *mut leanh::LeanObject,
    mut v_a_2512_: *mut leanh::LeanObject,
    mut v_a_2513_: *mut leanh::LeanObject,
    mut v_a_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Lean_Elab_TerminationMeasure_structuralArg(
        v_measure_2509_,
        v_a_2510_,
        v_a_2511_,
        v_a_2512_,
        v_a_2513_,
    );
    leanh::lean_dec(v_a_2513_);
    leanh::lean_dec_ref(v_a_2512_);
    leanh::lean_dec(v_a_2511_);
    leanh::lean_dec_ref(v_a_2510_);
    return v_res_2515_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(
    mut v___y_2516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_subExpr_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_subExpr_2518_ = leanh::lean_ctor_get(v___y_2516_, 3);
    v_expr_2519_ = leanh::lean_ctor_get(v_subExpr_2518_, 0);
    leanh::lean_inc_ref(v_expr_2519_);
    v___x_2520_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2520_, 0, v_expr_2519_);
    return v___x_2520_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg___boxed(
    mut v___y_2521_: *mut leanh::LeanObject,
    mut v___y_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2523_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_2521_);
    leanh::lean_dec_ref(v___y_2521_);
    return v_res_2523_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(
    mut v___y_2524_: *mut leanh::LeanObject,
    mut v___y_2525_: *mut leanh::LeanObject,
    mut v___y_2526_: *mut leanh::LeanObject,
    mut v___y_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2531_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_2524_);
    return v___x_2531_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___boxed(
    mut v___y_2532_: *mut leanh::LeanObject,
    mut v___y_2533_: *mut leanh::LeanObject,
    mut v___y_2534_: *mut leanh::LeanObject,
    mut v___y_2535_: *mut leanh::LeanObject,
    mut v___y_2536_: *mut leanh::LeanObject,
    mut v___y_2537_: *mut leanh::LeanObject,
    mut v___y_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
    leanh::lean_dec(v___y_2537_);
    leanh::lean_dec_ref(v___y_2536_);
    leanh::lean_dec(v___y_2535_);
    leanh::lean_dec_ref(v___y_2534_);
    leanh::lean_dec(v___y_2533_);
    leanh::lean_dec_ref(v___y_2532_);
    return v_res_2539_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(
    mut v_____do__lift_2540_: *mut leanh::LeanObject,
    mut v___y_2541_: *mut leanh::LeanObject,
    mut v___y_2542_: *mut leanh::LeanObject,
    mut v___y_2543_: *mut leanh::LeanObject,
    mut v___y_2544_: *mut leanh::LeanObject,
    mut v___y_2545_: *mut leanh::LeanObject,
    mut v___y_2546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2548_ = 0;
    v___x_2549_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2540_, v___x_2548_);
    v___x_2550_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2550_, 0, v___x_2549_);
    return v___x_2550_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0___boxed(
    mut v_____do__lift_2551_: *mut leanh::LeanObject,
    mut v___y_2552_: *mut leanh::LeanObject,
    mut v___y_2553_: *mut leanh::LeanObject,
    mut v___y_2554_: *mut leanh::LeanObject,
    mut v___y_2555_: *mut leanh::LeanObject,
    mut v___y_2556_: *mut leanh::LeanObject,
    mut v___y_2557_: *mut leanh::LeanObject,
    mut v___y_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2559_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_____do__lift_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
    leanh::lean_dec(v___y_2557_);
    leanh::lean_dec_ref(v___y_2556_);
    leanh::lean_dec(v___y_2555_);
    leanh::lean_dec_ref(v___y_2554_);
    leanh::lean_dec(v___y_2553_);
    leanh::lean_dec_ref(v___y_2552_);
    leanh::lean_dec(v_____do__lift_2551_);
    return v_res_2559_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(
    mut v_a_2569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2571_ = lean_array_get_size(v_a_2569_);
                v___x_2572_ = leanh::lean_unsigned_to_nat(0);
                v___x_2573_ = lean_nat_dec_eq(v___x_2571_, v___x_2572_);
                if v___x_2573_ == 0 {
                    v___x_2574_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4;
                    v___x_2575_ = leanh::lean_box(0);
                    v___x_2576_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2577_ = lean_nat_sub(v___x_2571_, v___x_2576_);
                    v___x_2578_ = lean_array_get_borrowed(v___x_2575_, v_a_2569_, v___x_2577_);
                    leanh::lean_dec(v___x_2577_);
                    leanh::lean_inc(v___x_2578_);
                    v___x_2579_ = l_Lean_Syntax_isOfKind(v___x_2578_, v___x_2574_);
                    if v___x_2579_ == 0 {
                        v___x_2580_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2580_, 0, v_a_2569_);
                        return v___x_2580_;
                    } else {
                        v___x_2581_ = lean_array_pop(v_a_2569_);
                        v_a_2569_ = v___x_2581_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_2583_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2583_, 0, v_a_2569_);
                    return v___x_2583_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___boxed(
    mut v_a_2584_: *mut leanh::LeanObject,
    mut v___y_2585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2586_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_2584_);
    return v_res_2586_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(
    mut v_a_2587_: *mut leanh::LeanObject,
    mut v___x_2588_: *mut leanh::LeanObject,
    mut v_sz_2589_: usize,
    mut v_i_2590_: usize,
    mut v_bs_2591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2592_: u8 = 0;
    let mut v_v_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: usize = 0;
    let mut v___x_2599_: usize = 0;
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2592_ = lean_usize_dec_lt(v_i_2590_, v_sz_2589_);
                if v___x_2592_ == 0 {
                    leanh::lean_dec(v___x_2588_);
                    return v_bs_2591_;
                } else {
                    v_v_2593_ = lean_array_uget(v_bs_2591_, v_i_2590_);
                    v___x_2594_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2595_ = lean_array_uset(v_bs_2591_, v_i_2590_, v___x_2594_);
                    v___x_2602_ = l_Lean_TSyntax_getId(v_v_2593_);
                    v___x_2603_ = l_Lean_Syntax_hasIdent(v___x_2602_, v_a_2587_);
                    leanh::lean_dec(v___x_2602_);
                    if v___x_2603_ == 0 {
                        leanh::lean_dec(v_v_2593_);
                        leanh::lean_inc(v___x_2588_);
                        v___y_2597_ = v___x_2588_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2597_ = v_v_2593_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2598_ = 1usize;
                v___x_2599_ = lean_usize_add(v_i_2590_, v___x_2598_);
                v___x_2600_ = lean_array_uset(v_bs_x27_2595_, v_i_2590_, v___y_2597_);
                v_i_2590_ = v___x_2599_;
                v_bs_2591_ = v___x_2600_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0___boxed(
    mut v_a_2604_: *mut leanh::LeanObject,
    mut v___x_2605_: *mut leanh::LeanObject,
    mut v_sz_2606_: *mut leanh::LeanObject,
    mut v_i_2607_: *mut leanh::LeanObject,
    mut v_bs_2608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2609_: usize = 0;
    let mut v_i_boxed_2610_: usize = 0;
    let mut v_res_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2609_ = leanh::lean_unbox_usize(v_sz_2606_);
    leanh::lean_dec(v_sz_2606_);
    v_i_boxed_2610_ = leanh::lean_unbox_usize(v_i_2607_);
    leanh::lean_dec(v_i_2607_);
    v_res_2611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_2604_, v___x_2605_, v_sz_boxed_2609_, v_i_boxed_2610_, v_bs_2608_);
    leanh::lean_dec(v_a_2604_);
    return v_res_2611_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2624_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_2624_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed(
    mut v_a_2627_: *mut leanh::LeanObject,
    mut v_measure_2628_: *mut leanh::LeanObject,
    mut v_n_2629_: *mut leanh::LeanObject,
    mut v_n_2630_: *mut leanh::LeanObject,
    mut v___y_2631_: *mut leanh::LeanObject,
    mut v___y_2632_: *mut leanh::LeanObject,
    mut v___y_2633_: *mut leanh::LeanObject,
    mut v___y_2634_: *mut leanh::LeanObject,
    mut v___y_2635_: *mut leanh::LeanObject,
    mut v___y_2636_: *mut leanh::LeanObject,
    mut v___y_2637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2638_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(v_a_2627_, v_measure_2628_, v_n_2629_, v_n_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
    leanh::lean_dec(v___y_2636_);
    leanh::lean_dec_ref(v___y_2635_);
    leanh::lean_dec(v___y_2634_);
    leanh::lean_dec_ref(v___y_2633_);
    leanh::lean_dec(v___y_2632_);
    leanh::lean_dec_ref(v___y_2631_);
    leanh::lean_dec(v_n_2629_);
    return v_res_2638_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(
    mut v_measure_2639_: *mut leanh::LeanObject,
    mut v_a_2640_: *mut leanh::LeanObject,
    mut v_a_2641_: *mut leanh::LeanObject,
    mut v_a_2642_: *mut leanh::LeanObject,
    mut v_a_2643_: *mut leanh::LeanObject,
    mut v_a_2644_: *mut leanh::LeanObject,
    mut v_a_2645_: *mut leanh::LeanObject,
    mut v_a_2646_: *mut leanh::LeanObject,
    mut v_a_2647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2650_: u8 = 0;
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2660_: usize = 0;
    let mut v___x_2661_: usize = 0;
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_structural_2664_: u8 = 0;
    let mut v_a_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: u8 = 0;
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2691_: u8 = 0;
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut v_isSharedCheck_2703_: u8 = 0;
    let mut v_a_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: u8 = 0;
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2711_: u8 = 0;
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2734_: u8 = 0;
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut v_a_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: u8 = 0;
    let mut v_one_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2649_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2650_ = lean_nat_dec_eq(v_a_2640_, v_zero_2649_);
                if v_isZero_2650_ == 1 {
                    v___x_2651_ = l_Lean_PrettyPrinter_Delaborator_delab(
                        v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_,
                    );
                    if leanh::lean_obj_tag(v___x_2651_) == 0 {
                        v_a_2652_ = leanh::lean_ctor_get(v___x_2651_, 0);
                        leanh::lean_inc(v_a_2652_);
                        leanh::lean_dec_ref_known(v___x_2651_, 1);
                        v_ref_2653_ = leanh::lean_ctor_get(v_a_2646_, 5);
                        v___x_2654_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_2653_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
                        v_a_2655_ = leanh::lean_ctor_get(v___x_2654_, 0);
                        leanh::lean_inc_n(v_a_2655_, 2);
                        leanh::lean_dec_ref(v___x_2654_);
                        v___x_2656_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4;
                        v___x_2657_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0;
                        v___x_2658_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2658_, 0, v_a_2655_);
                        leanh::lean_ctor_set(v___x_2658_, 1, v___x_2657_);
                        v___x_2659_ = l_Lean_Syntax_node1(v_a_2655_, v___x_2656_, v___x_2658_);
                        v_sz_2660_ = lean_array_size(v_a_2641_);
                        v___x_2661_ = 0usize;
                        v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_2652_, v___x_2659_, v_sz_2660_, v___x_2661_, v_a_2641_);
                        v___x_2663_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v___x_2662_);
                        if leanh::lean_obj_tag(v___x_2663_) == 0 {
                            v_structural_2664_ = leanh::lean_ctor_get_uint8(
                                v_measure_2639_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            );
                            leanh::lean_dec_ref(v_measure_2639_);
                            if v_structural_2664_ == 0 {
                                v_a_2665_ = leanh::lean_ctor_get(v___x_2663_, 0);
                                v_isSharedCheck_2703_ =
                                    (!leanh::lean_is_exclusive(v___x_2663_)) as u8;
                                if v_isSharedCheck_2703_ == 0 {
                                    v___x_2667_ = v___x_2663_;
                                    v_isShared_2668_ = v_isSharedCheck_2703_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2665_);
                                    leanh::lean_dec(v___x_2663_);
                                    v___x_2667_ = leanh::lean_box(0);
                                    v_isShared_2668_ = v_isSharedCheck_2703_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_2704_ = leanh::lean_ctor_get(v___x_2663_, 0);
                                leanh::lean_inc(v_a_2704_);
                                leanh::lean_dec_ref_known(v___x_2663_, 1);
                                v___x_2705_ = lean_array_get_size(v_a_2704_);
                                v___x_2706_ = lean_nat_dec_eq(v___x_2705_, v_zero_2649_);
                                if v___x_2706_ == 0 {
                                    v___x_2707_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_2653_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
                                    v_a_2708_ = leanh::lean_ctor_get(v___x_2707_, 0);
                                    v_isSharedCheck_2729_ =
                                        (!leanh::lean_is_exclusive(v___x_2707_)) as u8;
                                    if v_isSharedCheck_2729_ == 0 {
                                        v___x_2710_ = v___x_2707_;
                                        v_isShared_2711_ = v_isSharedCheck_2729_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2708_);
                                        leanh::lean_dec(v___x_2707_);
                                        v___x_2710_ = leanh::lean_box(0);
                                        v_isShared_2711_ = v_isSharedCheck_2729_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_2704_);
                                    v___x_2730_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_2653_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
                                    v_a_2731_ = leanh::lean_ctor_get(v___x_2730_, 0);
                                    v_isSharedCheck_2748_ =
                                        (!leanh::lean_is_exclusive(v___x_2730_)) as u8;
                                    if v_isSharedCheck_2748_ == 0 {
                                        v___x_2733_ = v___x_2730_;
                                        v_isShared_2734_ = v_isSharedCheck_2748_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2731_);
                                        leanh::lean_dec(v___x_2730_);
                                        v___x_2733_ = leanh::lean_box(0);
                                        v_isShared_2734_ = v_isSharedCheck_2748_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2652_);
                            leanh::lean_dec_ref(v_measure_2639_);
                            v_a_2749_ = leanh::lean_ctor_get(v___x_2663_, 0);
                            v_isSharedCheck_2756_ =
                                (!leanh::lean_is_exclusive(v___x_2663_)) as u8;
                            if v_isSharedCheck_2756_ == 0 {
                                v___x_2751_ = v___x_2663_;
                                v_isShared_2752_ = v_isSharedCheck_2756_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2749_);
                                leanh::lean_dec(v___x_2663_);
                                v___x_2751_ = leanh::lean_box(0);
                                v_isShared_2752_ = v_isSharedCheck_2756_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_2641_);
                        leanh::lean_dec_ref(v_measure_2639_);
                        return v___x_2651_;
                    }
                } else {
                    v___x_2757_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v_a_2642_);
                    v_a_2758_ = leanh::lean_ctor_get(v___x_2757_, 0);
                    leanh::lean_inc(v_a_2758_);
                    leanh::lean_dec_ref(v___x_2757_);
                    v___x_2759_ = l_Lean_Expr_isLambda(v_a_2758_);
                    leanh::lean_dec(v_a_2758_);
                    if v___x_2759_ == 0 {
                        v_a_2640_ = v_zero_2649_;
                        state = 0;
                        continue;
                    } else {
                        v_one_2761_ = leanh::lean_unsigned_to_nat(1);
                        v_n_2762_ = lean_nat_sub(v_a_2640_, v_one_2761_);
                        v___f_2763_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed as *mut core::ffi::c_void, 11, 3);
                        leanh::lean_closure_set(v___f_2763_, 0, v_a_2641_);
                        leanh::lean_closure_set(v___f_2763_, 1, v_measure_2639_);
                        leanh::lean_closure_set(v___f_2763_, 2, v_n_2762_);
                        v___x_2764_ = l_Lean_NameSet_empty;
                        v___x_2765_ =
                            l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(
                                v___f_2763_,
                                v_isZero_2650_,
                                v___x_2764_,
                                v_a_2642_,
                                v_a_2643_,
                                v_a_2644_,
                                v_a_2645_,
                                v_a_2646_,
                                v_a_2647_,
                            );
                        return v___x_2765_;
                    }
                }
            }
            1 => {
                v___x_2669_ = lean_array_get_size(v_a_2665_);
                v___x_2670_ = lean_nat_dec_eq(v___x_2669_, v_zero_2649_);
                if v___x_2670_ == 0 {
                    v___x_2671_ = l_Lean_SourceInfo_fromRef(v_ref_2653_, v___x_2670_);
                    v___x_2672_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3;
                    v___x_2673_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4;
                    leanh::lean_inc_n(v___x_2671_, 5);
                    v___x_2674_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2674_, 0, v___x_2671_);
                    leanh::lean_ctor_set(v___x_2674_, 1, v___x_2673_);
                    v___x_2675_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6;
                    v___x_2676_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once), _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
                    v___x_2677_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2677_, 0, v___x_2671_);
                    leanh::lean_ctor_set(v___x_2677_, 1, v___x_2675_);
                    leanh::lean_ctor_set(v___x_2677_, 2, v___x_2676_);
                    v___x_2678_ = l_Array_append___redArg(v___x_2676_, v_a_2665_);
                    leanh::lean_dec(v_a_2665_);
                    v___x_2679_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2679_, 0, v___x_2671_);
                    leanh::lean_ctor_set(v___x_2679_, 1, v___x_2675_);
                    leanh::lean_ctor_set(v___x_2679_, 2, v___x_2678_);
                    v___x_2680_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8;
                    v___x_2681_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2681_, 0, v___x_2671_);
                    leanh::lean_ctor_set(v___x_2681_, 1, v___x_2680_);
                    v___x_2682_ =
                        l_Lean_Syntax_node2(v___x_2671_, v___x_2675_, v___x_2679_, v___x_2681_);
                    v___x_2683_ = l_Lean_Syntax_node4(
                        v___x_2671_,
                        v___x_2672_,
                        v___x_2674_,
                        v___x_2677_,
                        v___x_2682_,
                        v_a_2652_,
                    );
                    if v_isShared_2668_ == 0 {
                        leanh::lean_ctor_set(v___x_2667_, 0, v___x_2683_);
                        v___x_2685_ = v___x_2667_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2686_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
                        v___x_2685_ = v_reuseFailAlloc_2686_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2667_);
                    leanh::lean_dec(v_a_2665_);
                    v___x_2687_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_2653_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
                    v_a_2688_ = leanh::lean_ctor_get(v___x_2687_, 0);
                    v_isSharedCheck_2702_ = (!leanh::lean_is_exclusive(v___x_2687_)) as u8;
                    if v_isSharedCheck_2702_ == 0 {
                        v___x_2690_ = v___x_2687_;
                        v_isShared_2691_ = v_isSharedCheck_2702_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2688_);
                        leanh::lean_dec(v___x_2687_);
                        v___x_2690_ = leanh::lean_box(0);
                        v_isShared_2691_ = v_isSharedCheck_2702_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2685_;
            }
            3 => {
                v___x_2692_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3;
                v___x_2693_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4;
                leanh::lean_inc_n(v_a_2688_, 2);
                v___x_2694_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2694_, 0, v_a_2688_);
                leanh::lean_ctor_set(v___x_2694_, 1, v___x_2693_);
                v___x_2695_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6;
                v___x_2696_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once), _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
                v___x_2697_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2697_, 0, v_a_2688_);
                leanh::lean_ctor_set(v___x_2697_, 1, v___x_2695_);
                leanh::lean_ctor_set(v___x_2697_, 2, v___x_2696_);
                leanh::lean_inc_ref(v___x_2697_);
                v___x_2698_ = l_Lean_Syntax_node4(
                    v_a_2688_,
                    v___x_2692_,
                    v___x_2694_,
                    v___x_2697_,
                    v___x_2697_,
                    v_a_2652_,
                );
                if v_isShared_2691_ == 0 {
                    leanh::lean_ctor_set(v___x_2690_, 0, v___x_2698_);
                    v___x_2700_ = v___x_2690_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
                    v___x_2700_ = v_reuseFailAlloc_2701_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2700_;
            }
            5 => {
                v___x_2712_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3;
                v___x_2713_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4;
                leanh::lean_inc_n(v_a_2708_, 6);
                v___x_2714_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2714_, 0, v_a_2708_);
                leanh::lean_ctor_set(v___x_2714_, 1, v___x_2713_);
                v___x_2715_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6;
                v___x_2716_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9;
                v___x_2717_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2717_, 0, v_a_2708_);
                leanh::lean_ctor_set(v___x_2717_, 1, v___x_2716_);
                v___x_2718_ = l_Lean_Syntax_node1(v_a_2708_, v___x_2715_, v___x_2717_);
                v___x_2719_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once), _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
                v___x_2720_ = l_Array_append___redArg(v___x_2719_, v_a_2704_);
                leanh::lean_dec(v_a_2704_);
                v___x_2721_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2721_, 0, v_a_2708_);
                leanh::lean_ctor_set(v___x_2721_, 1, v___x_2715_);
                leanh::lean_ctor_set(v___x_2721_, 2, v___x_2720_);
                v___x_2722_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8;
                v___x_2723_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2723_, 0, v_a_2708_);
                leanh::lean_ctor_set(v___x_2723_, 1, v___x_2722_);
                v___x_2724_ = l_Lean_Syntax_node2(v_a_2708_, v___x_2715_, v___x_2721_, v___x_2723_);
                v___x_2725_ = l_Lean_Syntax_node4(
                    v_a_2708_,
                    v___x_2712_,
                    v___x_2714_,
                    v___x_2718_,
                    v___x_2724_,
                    v_a_2652_,
                );
                if v_isShared_2711_ == 0 {
                    leanh::lean_ctor_set(v___x_2710_, 0, v___x_2725_);
                    v___x_2727_ = v___x_2710_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2728_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
                    v___x_2727_ = v_reuseFailAlloc_2728_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2727_;
            }
            7 => {
                v___x_2735_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3;
                v___x_2736_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4;
                leanh::lean_inc_n(v_a_2731_, 4);
                v___x_2737_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2737_, 0, v_a_2731_);
                leanh::lean_ctor_set(v___x_2737_, 1, v___x_2736_);
                v___x_2738_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6;
                v___x_2739_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9;
                v___x_2740_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2740_, 0, v_a_2731_);
                leanh::lean_ctor_set(v___x_2740_, 1, v___x_2739_);
                v___x_2741_ = l_Lean_Syntax_node1(v_a_2731_, v___x_2738_, v___x_2740_);
                v___x_2742_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once), _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
                v___x_2743_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2743_, 0, v_a_2731_);
                leanh::lean_ctor_set(v___x_2743_, 1, v___x_2738_);
                leanh::lean_ctor_set(v___x_2743_, 2, v___x_2742_);
                v___x_2744_ = l_Lean_Syntax_node4(
                    v_a_2731_,
                    v___x_2735_,
                    v___x_2737_,
                    v___x_2741_,
                    v___x_2743_,
                    v_a_2652_,
                );
                if v_isShared_2734_ == 0 {
                    leanh::lean_ctor_set(v___x_2733_, 0, v___x_2744_);
                    v___x_2746_ = v___x_2733_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2747_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
                    v___x_2746_ = v_reuseFailAlloc_2747_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2746_;
            }
            9 => {
                if v_isShared_2752_ == 0 {
                    v___x_2754_ = v___x_2751_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2755_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
                    v___x_2754_ = v_reuseFailAlloc_2755_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(
    mut v_a_2766_: *mut leanh::LeanObject,
    mut v_measure_2767_: *mut leanh::LeanObject,
    mut v_n_2768_: *mut leanh::LeanObject,
    mut v_n_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
    mut v___y_2771_: *mut leanh::LeanObject,
    mut v___y_2772_: *mut leanh::LeanObject,
    mut v___y_2773_: *mut leanh::LeanObject,
    mut v___y_2774_: *mut leanh::LeanObject,
    mut v___y_2775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2777_ = lean_array_push(v_a_2766_, v_n_2769_);
    v___x_2778_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_2767_, v_n_2768_, v___x_2777_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
    return v___x_2778_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed(
    mut v_measure_2779_: *mut leanh::LeanObject,
    mut v_a_2780_: *mut leanh::LeanObject,
    mut v_a_2781_: *mut leanh::LeanObject,
    mut v_a_2782_: *mut leanh::LeanObject,
    mut v_a_2783_: *mut leanh::LeanObject,
    mut v_a_2784_: *mut leanh::LeanObject,
    mut v_a_2785_: *mut leanh::LeanObject,
    mut v_a_2786_: *mut leanh::LeanObject,
    mut v_a_2787_: *mut leanh::LeanObject,
    mut v_a_2788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2789_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
    leanh::lean_dec(v_a_2787_);
    leanh::lean_dec_ref(v_a_2786_);
    leanh::lean_dec(v_a_2785_);
    leanh::lean_dec_ref(v_a_2784_);
    leanh::lean_dec(v_a_2783_);
    leanh::lean_dec_ref(v_a_2782_);
    leanh::lean_dec(v_a_2780_);
    return v_res_2789_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(
    mut v_inst_2790_: *mut leanh::LeanObject,
    mut v_a_2791_: *mut leanh::LeanObject,
    mut v___y_2792_: *mut leanh::LeanObject,
    mut v___y_2793_: *mut leanh::LeanObject,
    mut v___y_2794_: *mut leanh::LeanObject,
    mut v___y_2795_: *mut leanh::LeanObject,
    mut v___y_2796_: *mut leanh::LeanObject,
    mut v___y_2797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2799_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_2791_);
    return v___x_2799_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___boxed(
    mut v_inst_2800_: *mut leanh::LeanObject,
    mut v_a_2801_: *mut leanh::LeanObject,
    mut v___y_2802_: *mut leanh::LeanObject,
    mut v___y_2803_: *mut leanh::LeanObject,
    mut v___y_2804_: *mut leanh::LeanObject,
    mut v___y_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
    mut v___y_2807_: *mut leanh::LeanObject,
    mut v___y_2808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2809_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(v_inst_2800_, v_a_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
    leanh::lean_dec(v___y_2807_);
    leanh::lean_dec_ref(v___y_2806_);
    leanh::lean_dec(v___y_2805_);
    leanh::lean_dec_ref(v___y_2804_);
    leanh::lean_dec(v___y_2803_);
    leanh::lean_dec_ref(v___y_2802_);
    return v_res_2809_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(
    mut v_x_2810_: *mut leanh::LeanObject,
    mut v_x_2811_: *mut leanh::LeanObject,
    mut v_h__1_2812_: *mut leanh::LeanObject,
    mut v_h__2_2813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2815_: u8 = 0;
    v_zero_2814_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_2815_ = lean_nat_dec_eq(v_x_2810_, v_zero_2814_);
    if v_isZero_2815_ == 1 {
        let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2813_);
        v___x_2816_ = leanh::lean_apply_1(v_h__1_2812_, v_x_2811_);
        return v___x_2816_;
    } else {
        let mut v_one_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2812_);
        v_one_2817_ = leanh::lean_unsigned_to_nat(1);
        v_n_2818_ = lean_nat_sub(v_x_2810_, v_one_2817_);
        v___x_2819_ = leanh::lean_apply_2(v_h__2_2813_, v_n_2818_, v_x_2811_);
        return v___x_2819_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg___boxed(
    mut v_x_2820_: *mut leanh::LeanObject,
    mut v_x_2821_: *mut leanh::LeanObject,
    mut v_h__1_2822_: *mut leanh::LeanObject,
    mut v_h__2_2823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2824_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(v_x_2820_, v_x_2821_, v_h__1_2822_, v_h__2_2823_);
    leanh::lean_dec(v_x_2820_);
    return v_res_2824_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(
    mut v_motive_2825_: *mut leanh::LeanObject,
    mut v_x_2826_: *mut leanh::LeanObject,
    mut v_x_2827_: *mut leanh::LeanObject,
    mut v_h__1_2828_: *mut leanh::LeanObject,
    mut v_h__2_2829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2831_: u8 = 0;
    v_zero_2830_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_2831_ = lean_nat_dec_eq(v_x_2826_, v_zero_2830_);
    if v_isZero_2831_ == 1 {
        let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2829_);
        v___x_2832_ = leanh::lean_apply_1(v_h__1_2828_, v_x_2827_);
        return v___x_2832_;
    } else {
        let mut v_one_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2828_);
        v_one_2833_ = leanh::lean_unsigned_to_nat(1);
        v_n_2834_ = lean_nat_sub(v_x_2826_, v_one_2833_);
        v___x_2835_ = leanh::lean_apply_2(v_h__2_2829_, v_n_2834_, v_x_2827_);
        return v___x_2835_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___boxed(
    mut v_motive_2836_: *mut leanh::LeanObject,
    mut v_x_2837_: *mut leanh::LeanObject,
    mut v_x_2838_: *mut leanh::LeanObject,
    mut v_h__1_2839_: *mut leanh::LeanObject,
    mut v_h__2_2840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2841_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(v_motive_2836_, v_x_2837_, v_x_2838_, v_h__1_2839_, v_h__2_2840_);
    leanh::lean_dec(v_x_2837_);
    return v_res_2841_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter___redArg(
    mut v_x_2842_: *mut leanh::LeanObject,
    mut v_h__1_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = leanh::lean_apply_2(v_h__1_2843_, v_x_2842_, leanh::lean_box(0));
    return v___x_2844_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter(
    mut v_00_u03b1_2845_: *mut leanh::LeanObject,
    mut v_P_2846_: *mut leanh::LeanObject,
    mut v_motive_2847_: *mut leanh::LeanObject,
    mut v_x_2848_: *mut leanh::LeanObject,
    mut v_h__1_2849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2850_ = leanh::lean_apply_2(v_h__1_2849_, v_x_2848_, leanh::lean_box(0));
    return v___x_2850_;
}
pub unsafe fn l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(
    mut v_e_2851_: *mut leanh::LeanObject,
    mut v_maxFVars_2852_: *mut leanh::LeanObject,
    mut v_k_2853_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2854_: u8,
    mut v___y_2855_: *mut leanh::LeanObject,
    mut v___y_2856_: *mut leanh::LeanObject,
    mut v___y_2857_: *mut leanh::LeanObject,
    mut v___y_2858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: u8 = 0;
    let mut v___x_2862_: u8 = 0;
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2868_: u8 = 0;
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2872_: u8 = 0;
    let mut v_a_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2876_: u8 = 0;
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2860_ = leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2860_, 0, v_k_2853_);
                v___x_2861_ = 1;
                v___x_2862_ = 0;
                v___x_2863_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2863_, 0, v_maxFVars_2852_);
                v___x_2864_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    leanh::lean_box(0),
                    v_e_2851_,
                    v___x_2861_,
                    v___x_2862_,
                    v___x_2861_,
                    v___x_2862_,
                    v___x_2863_,
                    v___f_2860_,
                    v_cleanupAnnotations_2854_,
                    v___y_2855_,
                    v___y_2856_,
                    v___y_2857_,
                    v___y_2858_,
                );
                leanh::lean_dec_ref_known(v___x_2863_, 1);
                if leanh::lean_obj_tag(v___x_2864_) == 0 {
                    v_a_2865_ = leanh::lean_ctor_get(v___x_2864_, 0);
                    v_isSharedCheck_2872_ = (!leanh::lean_is_exclusive(v___x_2864_)) as u8;
                    if v_isSharedCheck_2872_ == 0 {
                        v___x_2867_ = v___x_2864_;
                        v_isShared_2868_ = v_isSharedCheck_2872_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2865_);
                        leanh::lean_dec(v___x_2864_);
                        v___x_2867_ = leanh::lean_box(0);
                        v_isShared_2868_ = v_isSharedCheck_2872_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2873_ = leanh::lean_ctor_get(v___x_2864_, 0);
                    v_isSharedCheck_2880_ = (!leanh::lean_is_exclusive(v___x_2864_)) as u8;
                    if v_isSharedCheck_2880_ == 0 {
                        v___x_2875_ = v___x_2864_;
                        v_isShared_2876_ = v_isSharedCheck_2880_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2873_);
                        leanh::lean_dec(v___x_2864_);
                        v___x_2875_ = leanh::lean_box(0);
                        v_isShared_2876_ = v_isSharedCheck_2880_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2868_ == 0 {
                    v___x_2870_ = v___x_2867_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2871_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
                    v___x_2870_ = v_reuseFailAlloc_2871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2870_;
            }
            3 => {
                if v_isShared_2876_ == 0 {
                    v___x_2878_ = v___x_2875_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2879_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
                    v___x_2878_ = v_reuseFailAlloc_2879_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg___boxed(
    mut v_e_2881_: *mut leanh::LeanObject,
    mut v_maxFVars_2882_: *mut leanh::LeanObject,
    mut v_k_2883_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
    mut v___y_2888_: *mut leanh::LeanObject,
    mut v___y_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2890_: u8 = 0;
    let mut v_res_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2890_ = (leanh::lean_unbox(v_cleanupAnnotations_2884_) as u8);
    v_res_2891_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_2881_, v_maxFVars_2882_, v_k_2883_, v_cleanupAnnotations_boxed_2890_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
    leanh::lean_dec(v___y_2888_);
    leanh::lean_dec_ref(v___y_2887_);
    leanh::lean_dec(v___y_2886_);
    leanh::lean_dec_ref(v___y_2885_);
    return v_res_2891_;
}
pub unsafe fn l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(
    mut v_00_u03b1_2892_: *mut leanh::LeanObject,
    mut v_e_2893_: *mut leanh::LeanObject,
    mut v_maxFVars_2894_: *mut leanh::LeanObject,
    mut v_k_2895_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2896_: u8,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___y_2898_: *mut leanh::LeanObject,
    mut v___y_2899_: *mut leanh::LeanObject,
    mut v___y_2900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2902_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_2893_, v_maxFVars_2894_, v_k_2895_, v_cleanupAnnotations_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
    return v___x_2902_;
}
pub unsafe fn l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___boxed(
    mut v_00_u03b1_2903_: *mut leanh::LeanObject,
    mut v_e_2904_: *mut leanh::LeanObject,
    mut v_maxFVars_2905_: *mut leanh::LeanObject,
    mut v_k_2906_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2907_: *mut leanh::LeanObject,
    mut v___y_2908_: *mut leanh::LeanObject,
    mut v___y_2909_: *mut leanh::LeanObject,
    mut v___y_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
    mut v___y_2912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2913_: u8 = 0;
    let mut v_res_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2913_ = (leanh::lean_unbox(v_cleanupAnnotations_2907_) as u8);
    v_res_2914_ =
        l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(
            v_00_u03b1_2903_,
            v_e_2904_,
            v_maxFVars_2905_,
            v_k_2906_,
            v_cleanupAnnotations_boxed_2913_,
            v___y_2908_,
            v___y_2909_,
            v___y_2910_,
            v___y_2911_,
        );
    leanh::lean_dec(v___y_2911_);
    leanh::lean_dec_ref(v___y_2910_);
    leanh::lean_dec(v___y_2909_);
    leanh::lean_dec_ref(v___y_2908_);
    return v_res_2914_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_delab___lam__0(
    mut v_measure_2917_: *mut leanh::LeanObject,
    mut v_extraParams_2918_: *mut leanh::LeanObject,
    mut v___ys_2919_: *mut leanh::LeanObject,
    mut v_e_2920_: *mut leanh::LeanObject,
    mut v___y_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
    mut v___y_2923_: *mut leanh::LeanObject,
    mut v___y_2924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2933_: u8 = 0;
    let mut v_fst_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2938_: u8 = 0;
    let mut v_a_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2942_: u8 = 0;
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2926_ = leanh::lean_box(1);
                v___x_2927_ = l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0;
                v___x_2928_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed as *mut core::ffi::c_void, 10, 3);
                leanh::lean_closure_set(v___x_2928_, 0, v_measure_2917_);
                leanh::lean_closure_set(v___x_2928_, 1, v_extraParams_2918_);
                leanh::lean_closure_set(v___x_2928_, 2, v___x_2927_);
                v___x_2929_ = l_Lean_PrettyPrinter_delabCore___redArg(
                    v_e_2920_,
                    v___x_2926_,
                    v___x_2928_,
                    v___y_2921_,
                    v___y_2922_,
                    v___y_2923_,
                    v___y_2924_,
                );
                if leanh::lean_obj_tag(v___x_2929_) == 0 {
                    v_a_2930_ = leanh::lean_ctor_get(v___x_2929_, 0);
                    v_isSharedCheck_2938_ = (!leanh::lean_is_exclusive(v___x_2929_)) as u8;
                    if v_isSharedCheck_2938_ == 0 {
                        v___x_2932_ = v___x_2929_;
                        v_isShared_2933_ = v_isSharedCheck_2938_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2930_);
                        leanh::lean_dec(v___x_2929_);
                        v___x_2932_ = leanh::lean_box(0);
                        v_isShared_2933_ = v_isSharedCheck_2938_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2939_ = leanh::lean_ctor_get(v___x_2929_, 0);
                    v_isSharedCheck_2946_ = (!leanh::lean_is_exclusive(v___x_2929_)) as u8;
                    if v_isSharedCheck_2946_ == 0 {
                        v___x_2941_ = v___x_2929_;
                        v_isShared_2942_ = v_isSharedCheck_2946_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2939_);
                        leanh::lean_dec(v___x_2929_);
                        v___x_2941_ = leanh::lean_box(0);
                        v_isShared_2942_ = v_isSharedCheck_2946_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2934_ = leanh::lean_ctor_get(v_a_2930_, 0);
                leanh::lean_inc(v_fst_2934_);
                leanh::lean_dec(v_a_2930_);
                if v_isShared_2933_ == 0 {
                    leanh::lean_ctor_set(v___x_2932_, 0, v_fst_2934_);
                    v___x_2936_ = v___x_2932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2937_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_fst_2934_);
                    v___x_2936_ = v_reuseFailAlloc_2937_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2936_;
            }
            3 => {
                if v_isShared_2942_ == 0 {
                    v___x_2944_ = v___x_2941_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2945_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
                    v___x_2944_ = v_reuseFailAlloc_2945_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed(
    mut v_measure_2947_: *mut leanh::LeanObject,
    mut v_extraParams_2948_: *mut leanh::LeanObject,
    mut v___ys_2949_: *mut leanh::LeanObject,
    mut v_e_2950_: *mut leanh::LeanObject,
    mut v___y_2951_: *mut leanh::LeanObject,
    mut v___y_2952_: *mut leanh::LeanObject,
    mut v___y_2953_: *mut leanh::LeanObject,
    mut v___y_2954_: *mut leanh::LeanObject,
    mut v___y_2955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2956_ = l_Lean_Elab_TerminationMeasure_delab___lam__0(
        v_measure_2947_,
        v_extraParams_2948_,
        v___ys_2949_,
        v_e_2950_,
        v___y_2951_,
        v___y_2952_,
        v___y_2953_,
        v___y_2954_,
    );
    leanh::lean_dec(v___y_2954_);
    leanh::lean_dec_ref(v___y_2953_);
    leanh::lean_dec(v___y_2952_);
    leanh::lean_dec_ref(v___y_2951_);
    leanh::lean_dec_ref(v___ys_2949_);
    return v_res_2956_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_delab(
    mut v_arity_2957_: *mut leanh::LeanObject,
    mut v_extraParams_2958_: *mut leanh::LeanObject,
    mut v_measure_2959_: *mut leanh::LeanObject,
    mut v_a_2960_: *mut leanh::LeanObject,
    mut v_a_2961_: *mut leanh::LeanObject,
    mut v_a_2962_: *mut leanh::LeanObject,
    mut v_a_2963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: u8 = 0;
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fn_2965_ = leanh::lean_ctor_get(v_measure_2959_, 1);
    leanh::lean_inc_ref(v_fn_2965_);
    leanh::lean_inc(v_extraParams_2958_);
    v___f_2966_ = leanh::lean_alloc_closure(
        l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    leanh::lean_closure_set(v___f_2966_, 0, v_measure_2959_);
    leanh::lean_closure_set(v___f_2966_, 1, v_extraParams_2958_);
    v___x_2967_ = lean_nat_sub(v_arity_2957_, v_extraParams_2958_);
    leanh::lean_dec(v_extraParams_2958_);
    v___x_2968_ = 0;
    v___x_2969_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_fn_2965_, v___x_2967_, v___f_2966_, v___x_2968_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
    return v___x_2969_;
}
pub unsafe fn l_Lean_Elab_TerminationMeasure_delab___boxed(
    mut v_arity_2970_: *mut leanh::LeanObject,
    mut v_extraParams_2971_: *mut leanh::LeanObject,
    mut v_measure_2972_: *mut leanh::LeanObject,
    mut v_a_2973_: *mut leanh::LeanObject,
    mut v_a_2974_: *mut leanh::LeanObject,
    mut v_a_2975_: *mut leanh::LeanObject,
    mut v_a_2976_: *mut leanh::LeanObject,
    mut v_a_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_Lean_Elab_TerminationMeasure_delab(
        v_arity_2970_,
        v_extraParams_2971_,
        v_measure_2972_,
        v_a_2973_,
        v_a_2974_,
        v_a_2975_,
        v_a_2976_,
    );
    leanh::lean_dec(v_a_2976_);
    leanh::lean_dec_ref(v_a_2975_);
    leanh::lean_dec(v_a_2974_);
    leanh::lean_dec_ref(v_a_2973_);
    leanh::lean_dec(v_arity_2970_);
    return v_res_2978_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Binders(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_instInhabitedTerminationMeasure_default =
        _init_l_Lean_Elab_instInhabitedTerminationMeasure_default();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedTerminationMeasure_default);
    l_Lean_Elab_instInhabitedTerminationMeasure =
        _init_l_Lean_Elab_instInhabitedTerminationMeasure();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedTerminationMeasure);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_TerminationMeasure(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_TerminationMeasure(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Binders(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
}
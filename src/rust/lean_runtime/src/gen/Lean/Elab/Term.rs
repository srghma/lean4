// Lean compiler output
// Module: Lean.Elab.Term
// Imports: Lean.Elab.DeclModifiers Lean.Elab.Term.TermElabM
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr3, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_ensureNoArgs, l_Lean_TagAttribute_hasTag,
    l_Lean_instBEqAttributeKind_beq, l_Lean_registerBuiltinAttribute, l_Lean_registerTagAttribute,
};
use crate::r#gen::Lean::Compiler::InitAttr::l_Lean_declareBuiltin;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::DeclModifiers::{
    initialize_Lean_Elab_DeclModifiers, l_Lean_Elab_expandDeclId,
    runtime_initialize_Lean_Elab_DeclModifiers,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    initialize_Lean_Elab_Term_TermElabM, runtime_initialize_Lean_Elab_Term_TermElabM,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_app___override, l_Lean_mkConst};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::ToExpr::l___private_Lean_ToExpr_0__Lean_Name_toExprAux;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_expandDeclId___closed__0_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
            110, 32, 110, 97, 109, 101, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_Term_expandDeclId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandDeclId___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_expandDeclId___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_expandDeclId___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_expandDeclId___closed__2_value: crate::leanh::LeanStringObject<50> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 50,
        m_capacity: 50,
        m_length: 49,
        m_data: [
            96, 44, 32, 116, 104, 101, 114, 101, 32, 105, 115, 32, 97, 32, 115, 101, 99, 116, 105,
            111, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 119, 105, 116, 104, 32, 116,
            104, 101, 32, 115, 97, 109, 101, 32, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Elab_Term_expandDeclId___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandDeclId___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_expandDeclId___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_expandDeclId___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 111, 115, 116, 112, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12403023605966109752 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11275091088550825312 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1949957779351256985 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14944671118004938876 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6361661000103932086 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16005925240757193755 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,923479786919109246 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12991445930590530375 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8763432369422750409 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15333080665684472645 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 111, 101, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15696008304709821516 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8686965749885275158 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__30_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 101, 117, 115, 101, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__30_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__30_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__30_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6536816683912670527 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11155329691653482754 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<238> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 238, m_capacity: 238, m_length: 237, m_data: [77, 97, 114, 107, 115, 32, 97, 110, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 32, 40, 116, 97, 99, 116, 105, 99, 32, 111, 114, 32, 99, 111, 109, 109, 97, 110, 100, 44, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 41, 32, 97, 115, 32, 115, 117, 112, 112, 111, 114, 116, 105, 110, 103, 32, 105, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 46, 32, 70, 111, 114, 32, 117, 110, 109, 97, 114, 107, 101, 100, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 115, 44, 32, 116, 104, 101, 32, 99, 111, 114, 114, 101, 115, 112, 111, 110, 100, 105, 110, 103, 32, 115, 110, 97, 112, 115, 104, 111, 116, 32, 98, 117, 110, 100, 108, 101, 32, 102, 105, 101, 108, 100, 32, 105, 110, 32, 116, 104, 101, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 32, 99, 111, 110, 116, 101, 120, 116, 32, 105, 115, 32, 117, 110, 115, 101, 116, 32, 115, 111, 32, 97, 115, 32, 116, 111, 32, 112, 114, 101, 118, 101, 110, 116, 32, 97, 99, 99, 105, 100, 101, 110, 116, 97, 108, 44, 32, 105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 114, 101, 117, 115, 101, 46, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [105, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14848544296075239282 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_incrementalAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0_value: crate::leanh::LeanStringObject<240> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 240, m_capacity: 240, m_length: 239, m_data: [77, 97, 114, 107, 115, 32, 97, 110, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 32, 40, 116, 97, 99, 116, 105, 99, 32, 111, 114, 32, 99, 111, 109, 109, 97, 110, 100, 44, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 41, 32, 97, 115, 32, 115, 117, 112, 112, 111, 114, 116, 105, 110, 103, 32, 105, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 46, 10, 10, 70, 111, 114, 32, 117, 110, 109, 97, 114, 107, 101, 100, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 115, 44, 32, 116, 104, 101, 32, 99, 111, 114, 114, 101, 115, 112, 111, 110, 100, 105, 110, 103, 32, 115, 110, 97, 112, 115, 104, 111, 116, 32, 98, 117, 110, 100, 108, 101, 32, 102, 105, 101, 108, 100, 32, 105, 110, 32, 116, 104, 101, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 32, 99, 111, 110, 116, 101, 120, 116, 32, 105, 115, 10, 117, 110, 115, 101, 116, 32, 115, 111, 32, 97, 115, 32, 116, 111, 32, 112, 114, 101, 118, 101, 110, 116, 32, 97, 99, 99, 105, 100, 101, 110, 116, 97, 108, 44, 32, 105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 114, 101, 117, 115, 101, 46, 10, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 40 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 88 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 88 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 37 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 37 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_builtinIncrementalElabs: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [97, 100, 100, 66, 117, 105, 108, 116, 105, 110, 73, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2114473129 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,2919963291769488560 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5850432591986621287 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17367040953597659823 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,2375789172174065578 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 105, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17192993897823996374 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 3, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [40, 98, 117, 105, 108, 116, 105, 110, 41, 32, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_isIncrementalElab___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_isIncrementalElab___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 70, 111, 114, 97, 108, 108, 0]};
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3958996631602752213 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = crate::leanh::lean_box(1);
    v___x_709_ = l_Lean_MessageData_ofFormat(v___x_708_);
    return v___x_709_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__2;
    v___x_714_ = l_Lean_MessageData_ofFormat(v___x_713_);
    return v___x_714_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3(
    mut v_x_715_: *mut crate::leanh::LeanObject,
    mut v_x_716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_721_: u8 = 0;
    let mut v_before_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_725_: u8 = 0;
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_738_: u8 = 0;
    let mut v_unused_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_716_) == 0 {
                    return v_x_715_;
                } else {
                    v_head_717_ = crate::leanh::lean_ctor_get(v_x_716_, 0);
                    v_tail_718_ = crate::leanh::lean_ctor_get(v_x_716_, 1);
                    v_isSharedCheck_740_ = (!crate::leanh::lean_is_exclusive(v_x_716_)) as u8;
                    if v_isSharedCheck_740_ == 0 {
                        v___x_720_ = v_x_716_;
                        v_isShared_721_ = v_isSharedCheck_740_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_718_);
                        crate::leanh::lean_inc(v_head_717_);
                        crate::leanh::lean_dec(v_x_716_);
                        v___x_720_ = crate::leanh::lean_box(0);
                        v_isShared_721_ = v_isSharedCheck_740_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_722_ = crate::leanh::lean_ctor_get(v_head_717_, 0);
                v_isSharedCheck_738_ = (!crate::leanh::lean_is_exclusive(v_head_717_)) as u8;
                if v_isSharedCheck_738_ == 0 {
                    v_unused_739_ = crate::leanh::lean_ctor_get(v_head_717_, 1);
                    crate::leanh::lean_dec(v_unused_739_);
                    v___x_724_ = v_head_717_;
                    v_isShared_725_ = v_isSharedCheck_738_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_722_);
                    crate::leanh::lean_dec(v_head_717_);
                    v___x_724_ = crate::leanh::lean_box(0);
                    v_isShared_725_ = v_isSharedCheck_738_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_726_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_725_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_724_, 7);
                    crate::leanh::lean_ctor_set(v___x_724_, 1, v___x_726_);
                    crate::leanh::lean_ctor_set(v___x_724_, 0, v_x_715_);
                    v___x_728_ = v___x_724_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_737_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_737_, 0, v_x_715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_726_);
                    v___x_728_ = v_reuseFailAlloc_737_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_729_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3);
                if v_isShared_721_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_720_, 7);
                    crate::leanh::lean_ctor_set(v___x_720_, 1, v___x_729_);
                    crate::leanh::lean_ctor_set(v___x_720_, 0, v___x_728_);
                    v___x_731_ = v___x_720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_736_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_729_);
                    v___x_731_ = v_reuseFailAlloc_736_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_732_ = l_Lean_MessageData_ofSyntax(v_before_722_);
                v___x_733_ = l_Lean_indentD(v___x_732_);
                v___x_734_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_734_, 0, v___x_731_);
                crate::leanh::lean_ctor_set(v___x_734_, 1, v___x_733_);
                v_x_715_ = v___x_734_;
                v_x_716_ = v_tail_718_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__2(
    mut v_opts_741_: *mut crate::leanh::LeanObject,
    mut v_opt_742_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_743_ = crate::leanh::lean_ctor_get(v_opt_742_, 0);
    v_defValue_744_ = crate::leanh::lean_ctor_get(v_opt_742_, 1);
    v_map_745_ = crate::leanh::lean_ctor_get(v_opts_741_, 0);
    v___x_746_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_745_,
            v_name_743_,
        );
    if crate::leanh::lean_obj_tag(v___x_746_) == 0 {
        let mut v___x_747_: u8 = 0;
        v___x_747_ = (crate::leanh::lean_unbox(v_defValue_744_) as u8);
        return v___x_747_;
    } else {
        let mut v_val_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_748_ = crate::leanh::lean_ctor_get(v___x_746_, 0);
        crate::leanh::lean_inc(v_val_748_);
        crate::leanh::lean_dec_ref_known(v___x_746_, 1);
        if crate::leanh::lean_obj_tag(v_val_748_) == 1 {
            let mut v_v_749_: u8 = 0;
            v_v_749_ = crate::leanh::lean_ctor_get_uint8(v_val_748_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_748_, 0);
            return v_v_749_;
        } else {
            let mut v___x_750_: u8 = 0;
            crate::leanh::lean_dec(v_val_748_);
            v___x_750_ = (crate::leanh::lean_unbox(v_defValue_744_) as u8);
            return v___x_750_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__2___boxed(
    mut v_opts_751_: *mut crate::leanh::LeanObject,
    mut v_opt_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_753_: u8 = 0;
    let mut v_r_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_753_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__2(v_opts_751_, v_opt_752_);
    crate::leanh::lean_dec_ref(v_opt_752_);
    crate::leanh::lean_dec_ref(v_opts_751_);
    v_r_754_ = crate::leanh::lean_box((v_res_753_) as usize);
    return v_r_754_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__1;
    v___x_759_ = l_Lean_MessageData_ofFormat(v___x_758_);
    return v___x_759_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(
    mut v_msgData_760_: *mut crate::leanh::LeanObject,
    mut v_macroStack_761_: *mut crate::leanh::LeanObject,
    mut v___y_762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: u8 = 0;
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_773_: u8 = 0;
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_785_: u8 = 0;
    let mut v_unused_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_764_ = crate::leanh::lean_ctor_get(v___y_762_, 2);
                v___x_765_ = l_Lean_Elab_pp_macroStack;
                v___x_766_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__2(v_options_764_, v___x_765_);
                if v___x_766_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_761_);
                    v___x_767_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_767_, 0, v_msgData_760_);
                    return v___x_767_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_761_) == 0 {
                        v___x_768_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_768_, 0, v_msgData_760_);
                        return v___x_768_;
                    } else {
                        v_head_769_ = crate::leanh::lean_ctor_get(v_macroStack_761_, 0);
                        crate::leanh::lean_inc(v_head_769_);
                        v_after_770_ = crate::leanh::lean_ctor_get(v_head_769_, 1);
                        v_isSharedCheck_785_ =
                            (!crate::leanh::lean_is_exclusive(v_head_769_)) as u8;
                        if v_isSharedCheck_785_ == 0 {
                            v_unused_786_ = crate::leanh::lean_ctor_get(v_head_769_, 0);
                            crate::leanh::lean_dec(v_unused_786_);
                            v___x_772_ = v_head_769_;
                            v_isShared_773_ = v_isSharedCheck_785_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_770_);
                            crate::leanh::lean_dec(v_head_769_);
                            v___x_772_ = crate::leanh::lean_box(0);
                            v_isShared_773_ = v_isSharedCheck_785_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_774_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_773_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_772_, 7);
                    crate::leanh::lean_ctor_set(v___x_772_, 1, v___x_774_);
                    crate::leanh::lean_ctor_set(v___x_772_, 0, v_msgData_760_);
                    v___x_776_ = v___x_772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_784_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_784_, 0, v_msgData_760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_774_);
                    v___x_776_ = v_reuseFailAlloc_784_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_777_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2);
                v___x_778_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_778_, 0, v___x_776_);
                crate::leanh::lean_ctor_set(v___x_778_, 1, v___x_777_);
                v___x_779_ = l_Lean_MessageData_ofSyntax(v_after_770_);
                v___x_780_ = l_Lean_indentD(v___x_779_);
                v_msgData_781_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_781_, 0, v___x_778_);
                crate::leanh::lean_ctor_set(v_msgData_781_, 1, v___x_780_);
                v___x_782_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3(v_msgData_781_, v_macroStack_761_);
                v___x_783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_783_, 0, v___x_782_);
                return v___x_783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___boxed(
    mut v_msgData_787_: *mut crate::leanh::LeanObject,
    mut v_macroStack_788_: *mut crate::leanh::LeanObject,
    mut v___y_789_: *mut crate::leanh::LeanObject,
    mut v___y_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(v_msgData_787_, v_macroStack_788_, v___y_789_);
    crate::leanh::lean_dec_ref(v___y_789_);
    return v_res_791_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0(
    mut v_msgData_792_: *mut crate::leanh::LeanObject,
    mut v___y_793_: *mut crate::leanh::LeanObject,
    mut v___y_794_: *mut crate::leanh::LeanObject,
    mut v___y_795_: *mut crate::leanh::LeanObject,
    mut v___y_796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = lean_st_ref_get(v___y_796_);
    v_env_799_ = crate::leanh::lean_ctor_get(v___x_798_, 0);
    crate::leanh::lean_inc_ref(v_env_799_);
    crate::leanh::lean_dec(v___x_798_);
    v___x_800_ = lean_st_ref_get(v___y_794_);
    v_mctx_801_ = crate::leanh::lean_ctor_get(v___x_800_, 0);
    crate::leanh::lean_inc_ref(v_mctx_801_);
    crate::leanh::lean_dec(v___x_800_);
    v_lctx_802_ = crate::leanh::lean_ctor_get(v___y_793_, 2);
    v_options_803_ = crate::leanh::lean_ctor_get(v___y_795_, 2);
    crate::leanh::lean_inc_ref(v_options_803_);
    crate::leanh::lean_inc_ref(v_lctx_802_);
    v___x_804_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_804_, 0, v_env_799_);
    crate::leanh::lean_ctor_set(v___x_804_, 1, v_mctx_801_);
    crate::leanh::lean_ctor_set(v___x_804_, 2, v_lctx_802_);
    crate::leanh::lean_ctor_set(v___x_804_, 3, v_options_803_);
    v___x_805_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_805_, 0, v___x_804_);
    crate::leanh::lean_ctor_set(v___x_805_, 1, v_msgData_792_);
    v___x_806_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_806_, 0, v___x_805_);
    return v___x_806_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0___boxed(
    mut v_msgData_807_: *mut crate::leanh::LeanObject,
    mut v___y_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
    mut v___y_810_: *mut crate::leanh::LeanObject,
    mut v___y_811_: *mut crate::leanh::LeanObject,
    mut v___y_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0(v_msgData_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
    crate::leanh::lean_dec(v___y_811_);
    crate::leanh::lean_dec_ref(v___y_810_);
    crate::leanh::lean_dec(v___y_809_);
    crate::leanh::lean_dec_ref(v___y_808_);
    return v_res_813_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(
    mut v_msg_814_: *mut crate::leanh::LeanObject,
    mut v___y_815_: *mut crate::leanh::LeanObject,
    mut v___y_816_: *mut crate::leanh::LeanObject,
    mut v___y_817_: *mut crate::leanh::LeanObject,
    mut v___y_818_: *mut crate::leanh::LeanObject,
    mut v___y_819_: *mut crate::leanh::LeanObject,
    mut v___y_820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_831_: u8 = 0;
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_822_ = crate::leanh::lean_ctor_get(v___y_819_, 5);
                v___x_823_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0(v_msg_814_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
                v_a_824_ = crate::leanh::lean_ctor_get(v___x_823_, 0);
                crate::leanh::lean_inc(v_a_824_);
                crate::leanh::lean_dec_ref(v___x_823_);
                v_macroStack_825_ = crate::leanh::lean_ctor_get(v___y_815_, 1);
                v___x_826_ = l_Lean_Elab_getBetterRef(v_ref_822_, v_macroStack_825_);
                crate::leanh::lean_inc(v_macroStack_825_);
                v___x_827_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(v_a_824_, v_macroStack_825_, v___y_819_);
                v_a_828_ = crate::leanh::lean_ctor_get(v___x_827_, 0);
                v_isSharedCheck_836_ = (!crate::leanh::lean_is_exclusive(v___x_827_)) as u8;
                if v_isSharedCheck_836_ == 0 {
                    v___x_830_ = v___x_827_;
                    v_isShared_831_ = v_isSharedCheck_836_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_828_);
                    crate::leanh::lean_dec(v___x_827_);
                    v___x_830_ = crate::leanh::lean_box(0);
                    v_isShared_831_ = v_isSharedCheck_836_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_832_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_832_, 0, v___x_826_);
                crate::leanh::lean_ctor_set(v___x_832_, 1, v_a_828_);
                if v_isShared_831_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_830_, 1);
                    crate::leanh::lean_ctor_set(v___x_830_, 0, v___x_832_);
                    v___x_834_ = v___x_830_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_835_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
                    v___x_834_ = v_reuseFailAlloc_835_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg___boxed(
    mut v_msg_837_: *mut crate::leanh::LeanObject,
    mut v___y_838_: *mut crate::leanh::LeanObject,
    mut v___y_839_: *mut crate::leanh::LeanObject,
    mut v___y_840_: *mut crate::leanh::LeanObject,
    mut v___y_841_: *mut crate::leanh::LeanObject,
    mut v___y_842_: *mut crate::leanh::LeanObject,
    mut v___y_843_: *mut crate::leanh::LeanObject,
    mut v___y_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_845_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(
        v_msg_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_,
    );
    crate::leanh::lean_dec(v___y_843_);
    crate::leanh::lean_dec_ref(v___y_842_);
    crate::leanh::lean_dec(v___y_841_);
    crate::leanh::lean_dec_ref(v___y_840_);
    crate::leanh::lean_dec(v___y_839_);
    crate::leanh::lean_dec_ref(v___y_838_);
    return v_res_845_;
}
pub unsafe fn _init_l_Lean_Elab_Term_expandDeclId___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = l_Lean_Elab_Term_expandDeclId___closed__0;
    v___x_848_ = l_Lean_stringToMessageData(v___x_847_);
    return v___x_848_;
}
pub unsafe fn _init_l_Lean_Elab_Term_expandDeclId___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = l_Lean_Elab_Term_expandDeclId___closed__2;
    v___x_851_ = l_Lean_stringToMessageData(v___x_850_);
    return v___x_851_;
}
pub unsafe fn l_Lean_Elab_Term_expandDeclId(
    mut v_currNamespace_852_: *mut crate::leanh::LeanObject,
    mut v_currLevelNames_853_: *mut crate::leanh::LeanObject,
    mut v_declId_854_: *mut crate::leanh::LeanObject,
    mut v_modifiers_855_: *mut crate::leanh::LeanObject,
    mut v_a_856_: *mut crate::leanh::LeanObject,
    mut v_a_857_: *mut crate::leanh::LeanObject,
    mut v_a_858_: *mut crate::leanh::LeanObject,
    mut v_a_859_: *mut crate::leanh::LeanObject,
    mut v_a_860_: *mut crate::leanh::LeanObject,
    mut v_a_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sectionVars_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shortName_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_877_: u8 = 0;
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_863_ = l_Lean_Elab_expandDeclId(
                    v_currNamespace_852_,
                    v_currLevelNames_853_,
                    v_declId_854_,
                    v_modifiers_855_,
                    v_a_856_,
                    v_a_857_,
                    v_a_858_,
                    v_a_859_,
                    v_a_860_,
                    v_a_861_,
                );
                if crate::leanh::lean_obj_tag(v___x_863_) == 0 {
                    v_a_864_ = crate::leanh::lean_ctor_get(v___x_863_, 0);
                    crate::leanh::lean_inc(v_a_864_);
                    v_sectionVars_865_ = crate::leanh::lean_ctor_get(v_a_856_, 4);
                    v_shortName_866_ = crate::leanh::lean_ctor_get(v_a_864_, 0);
                    crate::leanh::lean_inc(v_shortName_866_);
                    crate::leanh::lean_dec(v_a_864_);
                    v___x_867_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_shortName_866_, v_sectionVars_865_);
                    if v___x_867_ == 0 {
                        crate::leanh::lean_dec(v_shortName_866_);
                        return v___x_863_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_863_, 1);
                        v___x_868_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Term_expandDeclId___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_Elab_Term_expandDeclId___closed__1_once),
                            _init_l_Lean_Elab_Term_expandDeclId___closed__1,
                        );
                        v___x_869_ = l_Lean_MessageData_ofName(v_shortName_866_);
                        v___x_870_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_870_, 0, v___x_868_);
                        crate::leanh::lean_ctor_set(v___x_870_, 1, v___x_869_);
                        v___x_871_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Term_expandDeclId___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_Elab_Term_expandDeclId___closed__3_once),
                            _init_l_Lean_Elab_Term_expandDeclId___closed__3,
                        );
                        v___x_872_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_872_, 0, v___x_870_);
                        crate::leanh::lean_ctor_set(v___x_872_, 1, v___x_871_);
                        v___x_873_ =
                            l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(
                                v___x_872_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_,
                                v_a_861_,
                            );
                        v_a_874_ = crate::leanh::lean_ctor_get(v___x_873_, 0);
                        v_isSharedCheck_881_ = (!crate::leanh::lean_is_exclusive(v___x_873_)) as u8;
                        if v_isSharedCheck_881_ == 0 {
                            v___x_876_ = v___x_873_;
                            v_isShared_877_ = v_isSharedCheck_881_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_874_);
                            crate::leanh::lean_dec(v___x_873_);
                            v___x_876_ = crate::leanh::lean_box(0);
                            v_isShared_877_ = v_isSharedCheck_881_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_863_;
                }
            }
            1 => {
                if v_isShared_877_ == 0 {
                    v___x_879_ = v___x_876_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_880_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
                    v___x_879_ = v_reuseFailAlloc_880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_expandDeclId___boxed(
    mut v_currNamespace_882_: *mut crate::leanh::LeanObject,
    mut v_currLevelNames_883_: *mut crate::leanh::LeanObject,
    mut v_declId_884_: *mut crate::leanh::LeanObject,
    mut v_modifiers_885_: *mut crate::leanh::LeanObject,
    mut v_a_886_: *mut crate::leanh::LeanObject,
    mut v_a_887_: *mut crate::leanh::LeanObject,
    mut v_a_888_: *mut crate::leanh::LeanObject,
    mut v_a_889_: *mut crate::leanh::LeanObject,
    mut v_a_890_: *mut crate::leanh::LeanObject,
    mut v_a_891_: *mut crate::leanh::LeanObject,
    mut v_a_892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_893_ = l_Lean_Elab_Term_expandDeclId(
        v_currNamespace_882_,
        v_currLevelNames_883_,
        v_declId_884_,
        v_modifiers_885_,
        v_a_886_,
        v_a_887_,
        v_a_888_,
        v_a_889_,
        v_a_890_,
        v_a_891_,
    );
    crate::leanh::lean_dec(v_a_891_);
    crate::leanh::lean_dec_ref(v_a_890_);
    crate::leanh::lean_dec(v_a_889_);
    crate::leanh::lean_dec_ref(v_a_888_);
    crate::leanh::lean_dec(v_a_887_);
    crate::leanh::lean_dec_ref(v_a_886_);
    crate::leanh::lean_dec_ref(v_modifiers_885_);
    crate::leanh::lean_dec(v_declId_884_);
    return v_res_893_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0(
    mut v_00_u03b1_894_: *mut crate::leanh::LeanObject,
    mut v_msg_895_: *mut crate::leanh::LeanObject,
    mut v___y_896_: *mut crate::leanh::LeanObject,
    mut v___y_897_: *mut crate::leanh::LeanObject,
    mut v___y_898_: *mut crate::leanh::LeanObject,
    mut v___y_899_: *mut crate::leanh::LeanObject,
    mut v___y_900_: *mut crate::leanh::LeanObject,
    mut v___y_901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(
        v_msg_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_,
    );
    return v___x_903_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___boxed(
    mut v_00_u03b1_904_: *mut crate::leanh::LeanObject,
    mut v_msg_905_: *mut crate::leanh::LeanObject,
    mut v___y_906_: *mut crate::leanh::LeanObject,
    mut v___y_907_: *mut crate::leanh::LeanObject,
    mut v___y_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
    mut v___y_910_: *mut crate::leanh::LeanObject,
    mut v___y_911_: *mut crate::leanh::LeanObject,
    mut v___y_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_913_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0(
        v_00_u03b1_904_,
        v_msg_905_,
        v___y_906_,
        v___y_907_,
        v___y_908_,
        v___y_909_,
        v___y_910_,
        v___y_911_,
    );
    crate::leanh::lean_dec(v___y_911_);
    crate::leanh::lean_dec_ref(v___y_910_);
    crate::leanh::lean_dec(v___y_909_);
    crate::leanh::lean_dec_ref(v___y_908_);
    crate::leanh::lean_dec(v___y_907_);
    crate::leanh::lean_dec_ref(v___y_906_);
    return v_res_913_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1(
    mut v_msgData_914_: *mut crate::leanh::LeanObject,
    mut v_macroStack_915_: *mut crate::leanh::LeanObject,
    mut v___y_916_: *mut crate::leanh::LeanObject,
    mut v___y_917_: *mut crate::leanh::LeanObject,
    mut v___y_918_: *mut crate::leanh::LeanObject,
    mut v___y_919_: *mut crate::leanh::LeanObject,
    mut v___y_920_: *mut crate::leanh::LeanObject,
    mut v___y_921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_923_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(v_msgData_914_, v_macroStack_915_, v___y_920_);
    return v___x_923_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___boxed(
    mut v_msgData_924_: *mut crate::leanh::LeanObject,
    mut v_macroStack_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
    mut v___y_927_: *mut crate::leanh::LeanObject,
    mut v___y_928_: *mut crate::leanh::LeanObject,
    mut v___y_929_: *mut crate::leanh::LeanObject,
    mut v___y_930_: *mut crate::leanh::LeanObject,
    mut v___y_931_: *mut crate::leanh::LeanObject,
    mut v___y_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_933_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1(v_msgData_924_, v_macroStack_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
    crate::leanh::lean_dec(v___y_931_);
    crate::leanh::lean_dec_ref(v___y_930_);
    crate::leanh::lean_dec(v___y_929_);
    crate::leanh::lean_dec_ref(v___y_928_);
    crate::leanh::lean_dec(v___y_927_);
    crate::leanh::lean_dec_ref(v___y_926_);
    return v_res_933_;
}
pub unsafe fn _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_980_ = crate::leanh::lean_unsigned_to_nat(2544510742);
    v___x_981_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
    v___x_982_ = l_Lean_Name_num___override(v___x_981_, v___x_980_);
    return v___x_982_;
}
pub unsafe fn _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_984_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
    v___x_985_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
    v___x_986_ = l_Lean_Name_str___override(v___x_985_, v___x_984_);
    return v___x_986_;
}
pub unsafe fn _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
    v___x_989_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
    v___x_990_ = l_Lean_Name_str___override(v___x_989_, v___x_988_);
    return v___x_990_;
}
pub unsafe fn _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_992_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
    v___x_993_ = l_Lean_Name_num___override(v___x_992_, v___x_991_);
    return v___x_993_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: u8 = 0;
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1007_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
    v___x_1008_ = 0;
    v___x_1009_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
    v___x_1010_ = l_Lean_registerTraceClass(v___x_1007_, v___x_1008_, v___x_1009_);
    if crate::leanh::lean_obj_tag(v___x_1010_) == 0 {
        let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_1010_, 1);
        v___x_1011_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
        v___x_1012_ = l_Lean_registerTraceClass(v___x_1011_, v___x_1008_, v___x_1009_);
        if crate::leanh::lean_obj_tag(v___x_1012_) == 0 {
            let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_1012_, 1);
            v___x_1013_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
            v___x_1014_ = l_Lean_registerTraceClass(v___x_1013_, v___x_1008_, v___x_1009_);
            if crate::leanh::lean_obj_tag(v___x_1014_) == 0 {
                let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_1014_, 1);
                v___x_1015_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
                v___x_1016_ = l_Lean_registerTraceClass(v___x_1015_, v___x_1008_, v___x_1009_);
                return v___x_1016_;
            } else {
                return v___x_1014_;
            }
        } else {
            return v___x_1012_;
        }
    } else {
        return v___x_1010_;
    }
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2____boxed(
    mut v_a_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_();
    return v_res_1018_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_(
    mut v_x_1019_: *mut crate::leanh::LeanObject,
    mut v___y_1020_: *mut crate::leanh::LeanObject,
    mut v___y_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = crate::leanh::lean_box(0);
    v___x_1024_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1024_, 0, v___x_1023_);
    return v___x_1024_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2____boxed(
    mut v_x_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
    mut v___y_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1029_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_(v_x_1025_, v___y_1026_, v___y_1027_);
    crate::leanh::lean_dec(v___y_1027_);
    crate::leanh::lean_dec_ref(v___y_1026_);
    crate::leanh::lean_dec(v_x_1025_);
    return v_res_1029_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: u8 = 0;
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1041_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_;
    v___x_1042_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_;
    v___x_1043_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_;
    v___x_1044_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_;
    v___x_1045_ = 0;
    v___x_1046_ = crate::leanh::lean_box(2);
    v___x_1047_ = l_Lean_registerTagAttribute(
        v___x_1042_,
        v___x_1043_,
        v___f_1041_,
        v___x_1044_,
        v___x_1045_,
        v___x_1046_,
    );
    return v___x_1047_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2____boxed(
    mut v_a_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1049_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_();
    return v_res_1049_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_;
    v___x_1053_ = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0;
    v___x_1054_ = l_Lean_addBuiltinDocString(v___x_1052_, v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___boxed(
    mut v_a_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1();
    return v_res_1056_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_;
    v___x_1084_ = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__6;
    v___x_1085_ = l_Lean_addBuiltinDeclarationRanges(v___x_1083_, v___x_1084_);
    return v___x_1085_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___boxed(
    mut v_a_1086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1087_ = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3();
    return v_res_1087_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = l_Lean_NameSet_empty;
    v___x_1090_ = lean_st_mk_ref(v___x_1089_);
    v___x_1091_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1091_, 0, v___x_1090_);
    return v___x_1091_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2____boxed(
    mut v_a_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1093_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2_();
    return v_res_1093_;
}
pub unsafe fn l_Lean_Elab_addBuiltinIncrementalElab(
    mut v_decl_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1096_ = l_Lean_Elab_builtinIncrementalElabs;
    v___x_1097_ = lean_st_ref_take(v___x_1096_);
    v___x_1098_ = l_Lean_NameSet_insert(v___x_1097_, v_decl_1094_);
    v___x_1099_ = lean_st_ref_set(v___x_1096_, v___x_1098_);
    v___x_1100_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1100_, 0, v___x_1099_);
    return v___x_1100_;
}
pub unsafe fn l_Lean_Elab_addBuiltinIncrementalElab___boxed(
    mut v_decl_1101_: *mut crate::leanh::LeanObject,
    mut v_a_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1103_ = l_Lean_Elab_addBuiltinIncrementalElab(v_decl_1101_);
    return v_res_1103_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1104_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_1106_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1106_, 0, v___x_1105_);
    return v___x_1106_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_1108_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1109_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1109_, 0, v___x_1108_);
    crate::leanh::lean_ctor_set(v___x_1109_, 1, v___x_1108_);
    crate::leanh::lean_ctor_set(v___x_1109_, 2, v___x_1108_);
    crate::leanh::lean_ctor_set(v___x_1109_, 3, v___x_1108_);
    crate::leanh::lean_ctor_set(v___x_1109_, 4, v___x_1107_);
    crate::leanh::lean_ctor_set(v___x_1109_, 5, v___x_1107_);
    crate::leanh::lean_ctor_set(v___x_1109_, 6, v___x_1107_);
    crate::leanh::lean_ctor_set(v___x_1109_, 7, v___x_1107_);
    crate::leanh::lean_ctor_set(v___x_1109_, 8, v___x_1107_);
    crate::leanh::lean_ctor_set(v___x_1109_, 9, v___x_1107_);
    return v___x_1109_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1111_ = lean_mk_empty_array_with_capacity(v___x_1110_);
    v___x_1112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1112_, 0, v___x_1111_);
    return v___x_1112_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1113_: usize = 0;
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1113_ = 5usize;
    v___x_1114_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1115_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1116_ = lean_mk_empty_array_with_capacity(v___x_1115_);
    v___x_1117_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_1118_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1118_, 0, v___x_1117_);
    crate::leanh::lean_ctor_set(v___x_1118_, 1, v___x_1116_);
    crate::leanh::lean_ctor_set(v___x_1118_, 2, v___x_1114_);
    crate::leanh::lean_ctor_set(v___x_1118_, 3, v___x_1114_);
    crate::leanh::lean_ctor_set_usize(v___x_1118_, 4, v___x_1113_);
    return v___x_1118_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1119_ = crate::leanh::lean_box(1);
    v___x_1120_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_1121_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_1122_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1122_, 0, v___x_1121_);
    crate::leanh::lean_ctor_set(v___x_1122_, 1, v___x_1120_);
    crate::leanh::lean_ctor_set(v___x_1122_, 2, v___x_1119_);
    return v___x_1122_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_1123_: *mut crate::leanh::LeanObject,
    mut v___y_1124_: *mut crate::leanh::LeanObject,
    mut v___y_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = lean_st_ref_get(v___y_1125_);
    v_env_1128_ = crate::leanh::lean_ctor_get(v___x_1127_, 0);
    crate::leanh::lean_inc_ref(v_env_1128_);
    crate::leanh::lean_dec(v___x_1127_);
    v_options_1129_ = crate::leanh::lean_ctor_get(v___y_1124_, 2);
    v___x_1130_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_1131_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    crate::leanh::lean_inc_ref(v_options_1129_);
    v___x_1132_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1132_, 0, v_env_1128_);
    crate::leanh::lean_ctor_set(v___x_1132_, 1, v___x_1130_);
    crate::leanh::lean_ctor_set(v___x_1132_, 2, v___x_1131_);
    crate::leanh::lean_ctor_set(v___x_1132_, 3, v_options_1129_);
    v___x_1133_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1133_, 0, v___x_1132_);
    crate::leanh::lean_ctor_set(v___x_1133_, 1, v_msgData_1123_);
    v___x_1134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1134_, 0, v___x_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1139_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1135_, v___y_1136_, v___y_1137_);
    crate::leanh::lean_dec(v___y_1137_);
    crate::leanh::lean_dec_ref(v___y_1136_);
    return v_res_1139_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1149_: u8 = 0;
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1144_ = crate::leanh::lean_ctor_get(v___y_1141_, 5);
                v___x_1145_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0(v_msg_1140_, v___y_1141_, v___y_1142_);
                v_a_1146_ = crate::leanh::lean_ctor_get(v___x_1145_, 0);
                v_isSharedCheck_1154_ = (!crate::leanh::lean_is_exclusive(v___x_1145_)) as u8;
                if v_isSharedCheck_1154_ == 0 {
                    v___x_1148_ = v___x_1145_;
                    v_isShared_1149_ = v_isSharedCheck_1154_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1146_);
                    crate::leanh::lean_dec(v___x_1145_);
                    v___x_1148_ = crate::leanh::lean_box(0);
                    v_isShared_1149_ = v_isSharedCheck_1154_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1144_);
                v___x_1150_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1150_, 0, v_ref_1144_);
                crate::leanh::lean_ctor_set(v___x_1150_, 1, v_a_1146_);
                if v_isShared_1149_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1148_, 1);
                    crate::leanh::lean_ctor_set(v___x_1148_, 0, v___x_1150_);
                    v___x_1152_ = v___x_1148_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1153_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
                    v___x_1152_ = v_reuseFailAlloc_1153_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1152_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_1155_: *mut crate::leanh::LeanObject,
    mut v___y_1156_: *mut crate::leanh::LeanObject,
    mut v___y_1157_: *mut crate::leanh::LeanObject,
    mut v___y_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1159_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v_msg_1155_, v___y_1156_, v___y_1157_);
    crate::leanh::lean_dec(v___y_1157_);
    crate::leanh::lean_dec_ref(v___y_1156_);
    return v_res_1159_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__0;
    v___x_1162_ = l_Lean_stringToMessageData(v___x_1161_);
    return v___x_1162_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1164_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__2;
    v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
    return v___x_1165_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1167_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__4;
    v___x_1168_ = l_Lean_stringToMessageData(v___x_1167_);
    return v___x_1168_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(
    mut v_name_1172_: *mut crate::leanh::LeanObject,
    mut v_kind_1173_: u8,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1177_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1);
                v___x_1178_ = l_Lean_MessageData_ofName(v_name_1172_);
                v___x_1179_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1179_, 0, v___x_1177_);
                crate::leanh::lean_ctor_set(v___x_1179_, 1, v___x_1178_);
                v___x_1180_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3);
                v___x_1181_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1181_, 0, v___x_1179_);
                crate::leanh::lean_ctor_set(v___x_1181_, 1, v___x_1180_);
                match v_kind_1173_ {
                    0 => {
                        v___x_1190_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__6;
                        v___y_1183_ = v___x_1190_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_1191_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__7;
                        v___y_1183_ = v___x_1191_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1192_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__8;
                        v___y_1183_ = v___x_1192_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_1183_);
                v___x_1184_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1184_, 0, v___y_1183_);
                v___x_1185_ = l_Lean_MessageData_ofFormat(v___x_1184_);
                v___x_1186_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1186_, 0, v___x_1181_);
                crate::leanh::lean_ctor_set(v___x_1186_, 1, v___x_1185_);
                v___x_1187_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5);
                v___x_1188_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1188_, 0, v___x_1186_);
                crate::leanh::lean_ctor_set(v___x_1188_, 1, v___x_1187_);
                v___x_1189_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v___x_1188_, v___y_1174_, v___y_1175_);
                return v___x_1189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_name_1193_: *mut crate::leanh::LeanObject,
    mut v_kind_1194_: *mut crate::leanh::LeanObject,
    mut v___y_1195_: *mut crate::leanh::LeanObject,
    mut v___y_1196_: *mut crate::leanh::LeanObject,
    mut v___y_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_1198_: u8 = 0;
    let mut v_res_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1198_ = (crate::leanh::lean_unbox(v_kind_1194_) as u8);
    v_res_1199_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(v_name_1193_, v_kind_boxed_1198_, v___y_1195_, v___y_1196_);
    crate::leanh::lean_dec(v___y_1196_);
    crate::leanh::lean_dec_ref(v___y_1195_);
    return v_res_1199_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(
    mut v___x_1201_: *mut crate::leanh::LeanObject,
    mut v___x_1202_: *mut crate::leanh::LeanObject,
    mut v___x_1203_: *mut crate::leanh::LeanObject,
    mut v_decl_1204_: *mut crate::leanh::LeanObject,
    mut v_stx_1205_: *mut crate::leanh::LeanObject,
    mut v_kind_1206_: u8,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
    mut v___y_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: u8 = 0;
    let mut v___x_1222_: u8 = 0;
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1220_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1205_, v___y_1207_, v___y_1208_);
                if crate::leanh::lean_obj_tag(v___x_1220_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1220_, 1);
                    v___x_1221_ = 0;
                    v___x_1222_ = l_Lean_instBEqAttributeKind_beq(v_kind_1206_, v___x_1221_);
                    if v___x_1222_ == 0 {
                        crate::leanh::lean_dec(v_decl_1204_);
                        crate::leanh::lean_dec_ref(v___x_1202_);
                        crate::leanh::lean_dec_ref(v___x_1201_);
                        v___x_1223_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(v___x_1203_, v_kind_1206_, v___y_1207_, v___y_1208_);
                        return v___x_1223_;
                    } else {
                        crate::leanh::lean_dec(v___x_1203_);
                        v___y_1211_ = v___y_1207_;
                        v___y_1212_ = v___y_1208_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_decl_1204_);
                    crate::leanh::lean_dec(v___x_1203_);
                    crate::leanh::lean_dec_ref(v___x_1202_);
                    crate::leanh::lean_dec_ref(v___x_1201_);
                    return v___x_1220_;
                }
            }
            1 => {
                v___x_1213_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
                v___x_1214_ = l_Lean_Name_mkStr3(v___x_1201_, v___x_1202_, v___x_1213_);
                v___x_1215_ = crate::leanh::lean_box(0);
                v___x_1216_ = l_Lean_mkConst(v___x_1214_, v___x_1215_);
                crate::leanh::lean_inc(v_decl_1204_);
                v___x_1217_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_decl_1204_);
                v___x_1218_ = l_Lean_Expr_app___override(v___x_1216_, v___x_1217_);
                v___x_1219_ =
                    l_Lean_declareBuiltin(v_decl_1204_, v___x_1218_, v___y_1211_, v___y_1212_);
                return v___x_1219_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(
    mut v___x_1224_: *mut crate::leanh::LeanObject,
    mut v___x_1225_: *mut crate::leanh::LeanObject,
    mut v___x_1226_: *mut crate::leanh::LeanObject,
    mut v_decl_1227_: *mut crate::leanh::LeanObject,
    mut v_stx_1228_: *mut crate::leanh::LeanObject,
    mut v_kind_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
    mut v___y_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_1233_: u8 = 0;
    let mut v_res_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1233_ = (crate::leanh::lean_unbox(v_kind_1229_) as u8);
    v_res_1234_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(v___x_1224_, v___x_1225_, v___x_1226_, v_decl_1227_, v_stx_1228_, v_kind_boxed_1233_, v___y_1230_, v___y_1231_);
    crate::leanh::lean_dec(v___y_1231_);
    crate::leanh::lean_dec_ref(v___y_1230_);
    return v_res_1234_;
}
pub unsafe fn _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
    v___x_1237_ = l_Lean_stringToMessageData(v___x_1236_);
    return v___x_1237_;
}
pub unsafe fn _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1239_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
    v___x_1240_ = l_Lean_stringToMessageData(v___x_1239_);
    return v___x_1240_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(
    mut v___x_1241_: *mut crate::leanh::LeanObject,
    mut v_decl_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_);
    v___x_1247_ = l_Lean_MessageData_ofName(v___x_1241_);
    v___x_1248_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1248_, 0, v___x_1246_);
    crate::leanh::lean_ctor_set(v___x_1248_, 1, v___x_1247_);
    v___x_1249_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_);
    v___x_1250_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1250_, 0, v___x_1248_);
    crate::leanh::lean_ctor_set(v___x_1250_, 1, v___x_1249_);
    v___x_1251_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v___x_1250_, v___y_1243_, v___y_1244_);
    return v___x_1251_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(
    mut v___x_1252_: *mut crate::leanh::LeanObject,
    mut v_decl_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1257_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(v___x_1252_, v_decl_1253_, v___y_1254_, v___y_1255_);
    crate::leanh::lean_dec(v___y_1255_);
    crate::leanh::lean_dec_ref(v___y_1254_);
    crate::leanh::lean_dec(v_decl_1253_);
    return v_res_1257_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAttributeImplCore_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: u8 = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_Lean_Elab_incrementalAttr;
    v_attr_1282_ = crate::leanh::lean_ctor_get(v___x_1281_, 0);
    v_toAttributeImplCore_1283_ = crate::leanh::lean_ctor_get(v_attr_1282_, 0);
    v_descr_1284_ = crate::leanh::lean_ctor_get(v_toAttributeImplCore_1283_, 2);
    v___x_1285_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
    v___x_1286_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
    v___f_1287_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
    v___f_1288_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
    v___x_1289_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
    v___x_1290_ = lean_string_append(v___x_1289_, v_descr_1284_);
    v___x_1291_ = 1;
    v___x_1292_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1292_, 0, v___x_1285_);
    crate::leanh::lean_ctor_set(v___x_1292_, 1, v___x_1286_);
    crate::leanh::lean_ctor_set(v___x_1292_, 2, v___x_1290_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1292_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1291_,
    );
    v___x_1293_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1293_, 0, v___x_1292_);
    crate::leanh::lean_ctor_set(v___x_1293_, 1, v___f_1287_);
    crate::leanh::lean_ctor_set(v___x_1293_, 2, v___f_1288_);
    v___x_1294_ = l_Lean_registerBuiltinAttribute(v___x_1293_);
    return v___x_1294_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(
    mut v_a_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
    return v_res_1296_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_1297_: *mut crate::leanh::LeanObject,
    mut v_msg_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v_msg_1298_, v___y_1299_, v___y_1300_);
    return v___x_1302_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_1303_: *mut crate::leanh::LeanObject,
    mut v_msg_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1308_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0(v_00_u03b1_1303_, v_msg_1304_, v___y_1305_, v___y_1306_);
    crate::leanh::lean_dec(v___y_1306_);
    crate::leanh::lean_dec_ref(v___y_1305_);
    return v_res_1308_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_1309_: *mut crate::leanh::LeanObject,
    mut v_name_1310_: *mut crate::leanh::LeanObject,
    mut v_kind_1311_: u8,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(v_name_1310_, v_kind_1311_, v___y_1312_, v___y_1313_);
    return v___x_1315_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_1316_: *mut crate::leanh::LeanObject,
    mut v_name_1317_: *mut crate::leanh::LeanObject,
    mut v_kind_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_1322_: u8 = 0;
    let mut v_res_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1322_ = (crate::leanh::lean_unbox(v_kind_1318_) as u8);
    v_res_1323_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1(v_00_u03b1_1316_, v_name_1317_, v_kind_boxed_1322_, v___y_1319_, v___y_1320_);
    crate::leanh::lean_dec(v___y_1320_);
    crate::leanh::lean_dec_ref(v___y_1319_);
    return v_res_1323_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
    v___x_1326_ = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0;
    v___x_1327_ = l_Lean_addBuiltinDocString(v___x_1325_, v___x_1326_);
    return v___x_1327_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(
    mut v_a_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1329_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
    return v_res_1329_;
}
pub unsafe fn l_Lean_Elab_isIncrementalElab___redArg___lam__0(
    mut v___x_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = lean_st_ref_get(v___x_1330_);
    v___x_1333_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1332_);
    return v___x_1333_;
}
pub unsafe fn l_Lean_Elab_isIncrementalElab___redArg___lam__0___boxed(
    mut v___x_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Lean_Elab_isIncrementalElab___redArg___lam__0(v___x_1334_);
    crate::leanh::lean_dec(v___x_1334_);
    return v_res_1336_;
}
pub unsafe fn l_Lean_Elab_isIncrementalElab___redArg___lam__1(
    mut v_decl_1337_: *mut crate::leanh::LeanObject,
    mut v_toPure_1338_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1340_: u8 = 0;
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1340_ = l_Lean_NameSet_contains(v_____do__lift_1339_, v_decl_1337_);
    v___x_1341_ = crate::leanh::lean_box((v___x_1340_) as usize);
    v___x_1342_ =
        crate::leanh::lean_apply_2(v_toPure_1338_, crate::leanh::lean_box(0), v___x_1341_);
    return v___x_1342_;
}
pub unsafe fn l_Lean_Elab_isIncrementalElab___redArg___lam__1___boxed(
    mut v_decl_1343_: *mut crate::leanh::LeanObject,
    mut v_toPure_1344_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_Lean_Elab_isIncrementalElab___redArg___lam__1(
        v_decl_1343_,
        v_toPure_1344_,
        v_____do__lift_1345_,
    );
    crate::leanh::lean_dec(v_____do__lift_1345_);
    crate::leanh::lean_dec(v_decl_1343_);
    return v_res_1346_;
}
pub unsafe fn l_Lean_Elab_isIncrementalElab___redArg___lam__2(
    mut v_decl_1347_: *mut crate::leanh::LeanObject,
    mut v_toPure_1348_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1350_ = l_Lean_Elab_incrementalAttr;
    v___x_1351_ = l_Lean_TagAttribute_hasTag(v___x_1350_, v_____do__lift_1349_, v_decl_1347_);
    v___x_1352_ = crate::leanh::lean_box((v___x_1351_) as usize);
    v___x_1353_ =
        crate::leanh::lean_apply_2(v_toPure_1348_, crate::leanh::lean_box(0), v___x_1352_);
    return v___x_1353_;
}
pub unsafe fn l_Lean_Elab_isIncrementalElab___redArg___lam__3(
    mut v_inst_1354_: *mut crate::leanh::LeanObject,
    mut v_toBind_1355_: *mut crate::leanh::LeanObject,
    mut v___f_1356_: *mut crate::leanh::LeanObject,
    mut v_toPure_1357_: *mut crate::leanh::LeanObject,
    mut v_b_1358_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_b_1358_ == 0 {
        let mut v_getEnv_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1357_);
        v_getEnv_1359_ = crate::leanh::lean_ctor_get(v_inst_1354_, 0);
        crate::leanh::lean_inc(v_getEnv_1359_);
        crate::leanh::lean_dec_ref(v_inst_1354_);
        v___x_1360_ = crate::leanh::lean_apply_4(
            v_toBind_1355_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1359_,
            v___f_1356_,
        );
        return v___x_1360_;
    } else {
        let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_1356_);
        crate::leanh::lean_dec(v_toBind_1355_);
        crate::leanh::lean_dec_ref(v_inst_1354_);
        v___x_1361_ = crate::leanh::lean_box((v_b_1358_) as usize);
        v___x_1362_ =
            crate::leanh::lean_apply_2(v_toPure_1357_, crate::leanh::lean_box(0), v___x_1361_);
        return v___x_1362_;
    }
}
pub unsafe fn l_Lean_Elab_isIncrementalElab___redArg___lam__3___boxed(
    mut v_inst_1363_: *mut crate::leanh::LeanObject,
    mut v_toBind_1364_: *mut crate::leanh::LeanObject,
    mut v___f_1365_: *mut crate::leanh::LeanObject,
    mut v_toPure_1366_: *mut crate::leanh::LeanObject,
    mut v_b_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1368_: u8 = 0;
    let mut v_res_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1368_ = (crate::leanh::lean_unbox(v_b_1367_) as u8);
    v_res_1369_ = l_Lean_Elab_isIncrementalElab___redArg___lam__3(
        v_inst_1363_,
        v_toBind_1364_,
        v___f_1365_,
        v_toPure_1366_,
        v_b_boxed_1368_,
    );
    return v_res_1369_;
}
pub unsafe fn _init_l_Lean_Elab_isIncrementalElab___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = l_Lean_Elab_builtinIncrementalElabs;
    v___f_1371_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_isIncrementalElab___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1371_, 0, v___x_1370_);
    return v___f_1371_;
}
pub unsafe fn l_Lean_Elab_isIncrementalElab___redArg(
    mut v_inst_1372_: *mut crate::leanh::LeanObject,
    mut v_inst_1373_: *mut crate::leanh::LeanObject,
    mut v_inst_1374_: *mut crate::leanh::LeanObject,
    mut v_decl_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1376_ = crate::leanh::lean_ctor_get(v_inst_1372_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1376_);
    v_toBind_1377_ = crate::leanh::lean_ctor_get(v_inst_1372_, 1);
    crate::leanh::lean_inc_n(v_toBind_1377_, 3);
    crate::leanh::lean_dec_ref(v_inst_1372_);
    v_toPure_1378_ = crate::leanh::lean_ctor_get(v_toApplicative_1376_, 1);
    crate::leanh::lean_inc_n(v_toPure_1378_, 3);
    crate::leanh::lean_dec_ref(v_toApplicative_1376_);
    v___f_1379_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_isIncrementalElab___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_isIncrementalElab___redArg___closed__0_once),
        _init_l_Lean_Elab_isIncrementalElab___redArg___closed__0,
    );
    v___x_1380_ = crate::leanh::lean_apply_2(v_inst_1374_, crate::leanh::lean_box(0), v___f_1379_);
    crate::leanh::lean_inc(v_decl_1375_);
    v___f_1381_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_isIncrementalElab___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1381_, 0, v_decl_1375_);
    crate::leanh::lean_closure_set(v___f_1381_, 1, v_toPure_1378_);
    v___f_1382_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_isIncrementalElab___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1382_, 0, v_decl_1375_);
    crate::leanh::lean_closure_set(v___f_1382_, 1, v_toPure_1378_);
    v___f_1383_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_isIncrementalElab___redArg___lam__3___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1383_, 0, v_inst_1373_);
    crate::leanh::lean_closure_set(v___f_1383_, 1, v_toBind_1377_);
    crate::leanh::lean_closure_set(v___f_1383_, 2, v___f_1382_);
    crate::leanh::lean_closure_set(v___f_1383_, 3, v_toPure_1378_);
    v___x_1384_ = crate::leanh::lean_apply_4(
        v_toBind_1377_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1380_,
        v___f_1381_,
    );
    v___x_1385_ = crate::leanh::lean_apply_4(
        v_toBind_1377_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1384_,
        v___f_1383_,
    );
    return v___x_1385_;
}
pub unsafe fn l_Lean_Elab_isIncrementalElab(
    mut v_m_1386_: *mut crate::leanh::LeanObject,
    mut v_inst_1387_: *mut crate::leanh::LeanObject,
    mut v_inst_1388_: *mut crate::leanh::LeanObject,
    mut v_inst_1389_: *mut crate::leanh::LeanObject,
    mut v_decl_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = l_Lean_Elab_isIncrementalElab___redArg(
        v_inst_1387_,
        v_inst_1388_,
        v_inst_1389_,
        v_decl_1390_,
    );
    return v___x_1391_;
}
pub unsafe fn _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = crate::leanh::lean_unsigned_to_nat(3314678858);
    v___x_1397_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
    v___x_1398_ = l_Lean_Name_num___override(v___x_1397_, v___x_1396_);
    return v___x_1398_;
}
pub unsafe fn _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
    v___x_1400_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
    v___x_1401_ = l_Lean_Name_str___override(v___x_1400_, v___x_1399_);
    return v___x_1401_;
}
pub unsafe fn _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
    v___x_1403_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
    v___x_1404_ = l_Lean_Name_str___override(v___x_1403_, v___x_1402_);
    return v___x_1404_;
}
pub unsafe fn _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1406_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
    v___x_1407_ = l_Lean_Name_num___override(v___x_1406_, v___x_1405_);
    return v___x_1407_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_;
    v___x_1410_ = 0;
    v___x_1411_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
    v___x_1412_ = l_Lean_registerTraceClass(v___x_1409_, v___x_1410_, v___x_1411_);
    return v___x_1412_;
}
pub unsafe fn l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2____boxed(
    mut v_a_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1414_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_();
    return v_res_1414_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Term(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_DeclModifiers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_incrementalAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_incrementalAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_builtinIncrementalElabs = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_builtinIncrementalElabs);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Term(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Term(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_DeclModifiers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Term_TermElabM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Term(builtin);
}

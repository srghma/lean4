// Lean compiler output
// Module: Lake.DSL.Config
// Imports: Lean.Elab.Term Lake.DSL.Extensions Lake.DSL.Syntax Lake.Util.Name
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkApp,
    l_Lean_Syntax_mkCApp, l_Lean_Syntax_mkNameLit, l_Lean_Syntax_mkNumLit, l_Lean_Syntax_mkStrLit,
    l_Lean_TSyntax_getId, l_Lean_mkCIdentFrom, l_Lean_quoteNameMk, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node5, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lake::DSL::DeclUtil::l_Lake_DSL_packageDeclName;
use crate::r#gen::Lake::DSL::Extensions::{
    initialize_Lake_DSL_Extensions, l_Lake_dirExt, l_Lake_nameExt, l_Lake_optsExt,
    runtime_initialize_Lake_DSL_Extensions,
};
use crate::r#gen::Lake::DSL::Syntax::{
    initialize_Lake_DSL_Syntax, runtime_initialize_Lake_DSL_Syntax,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, l_Lake_Name_quoteFrom, runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm___boxed, l_Lean_Elab_Term_termElabAttribute,
    l_Lean_Elab_Term_tryPostponeIfNoneOrMVar, l_Lean_Elab_Term_withPushMacroExpansionStack___boxed,
};
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_Environment_contains,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7,
    lean_apply_8, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2_value:
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
    m_data: [110, 117, 109, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1_value)
            as *mut LeanObject,
        13306843946249674491 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value: LeanCtorObject<
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2_value)
            as *mut LeanObject,
        7229350633979142691 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 114, 105, 103, 78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8_value:
    LeanStringObject<60> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 60,
    m_capacity: 60,
    m_length: 59,
    m_data: [
        96, 95, 95, 110, 97, 109, 101, 95, 95, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98,
        101, 32, 117, 115, 101, 100, 32, 97, 102, 116, 101, 114, 32, 116, 104, 101, 32, 96, 112,
        97, 99, 107, 97, 103, 101, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 83, 76, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2_value) as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2_value) as *mut LeanObject,12277407653222002017 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut LeanObject,12997130533650095963 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut LeanObject,11286550318989764116 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8_value) as *mut LeanObject,14379505912603517747 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,13383813871919401118 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut LeanObject,3116803351010944398 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut LeanObject,17570291170315793637 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 108, 97, 98, 78, 97, 109, 101, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13_value) as *mut LeanObject,18216179882849010034 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14_value) as *mut LeanObject;
pub static l_Lake_DSL_dummyDir___closed__0_value: LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lake_DSL_dummyDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dummyDir___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_DSL_dummyDir: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dummyDir___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0_value:
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
    m_data: [83, 121, 115, 116, 101, 109, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [70, 105, 108, 101, 80, 97, 116, 104, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [109, 107, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0_value)
            as *mut LeanObject,
        3794196532276496372 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1_value)
            as *mut LeanObject,
        16862427096323398393 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value: LeanCtorObject<
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2_value)
            as *mut LeanObject,
        12740738272846701813 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [105, 100, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5_value: LeanCtorObject<
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4_value)
            as *mut LeanObject,
        6041859491766292191 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 117, 109, 109, 121, 68, 105, 114, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value: LeanCtorObject<
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6_value)
            as *mut LeanObject,
        12345917602089148072 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 105, 114, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0_value) as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0_value) as *mut LeanObject,14737761738784435815 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 68, 105, 114, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2_value) as *mut LeanObject,2474536823929498258 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [103, 101, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value: LeanCtorObject<
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0_value)
            as *mut LeanObject,
        6629962664469725265 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value:
    LeanStringObject<5> = LeanStringObject {
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
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4_value:
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
    m_data: [97, 112, 112, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_2:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value: LeanCtorObject<
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4_value)
            as *mut LeanObject,
        12966880221525079621 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 111, 109, 101, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8_value: LeanCtorObject<
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value)
            as *mut LeanObject,
        15308379890181982757 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value:
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
    m_data: [79, 112, 116, 105, 111, 110, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value)
            as *mut LeanObject,
        18184376426117065311 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value)
            as *mut LeanObject,
        4893146552088433753 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_2:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15_value
        ) as *mut LeanObject,
        5346268661279150583 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_2:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17_value
        ) as *mut LeanObject,
        7306243862518720553 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19_value:
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
    m_data: [40, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20_value
        ) as *mut LeanObject,
        9871775667037945883 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [69, 108, 97, 98, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value
        ) as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
            as *mut LeanObject,
        7892421401833366012 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value
        ) as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 111, 110, 101, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value
        ) as *mut LeanObject,
        17416048715816169289 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value)
            as *mut LeanObject,
        18184376426117065311 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value
        ) as *mut LeanObject,
        9480010471355609749 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42_value:
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
    m_data: [58, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value)
            as *mut LeanObject,
        18184376426117065311 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value)
            as *mut LeanObject,
        3127099019797772086 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52_value:
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
    m_data: [83, 116, 114, 105, 110, 103, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52_value
        ) as *mut LeanObject,
        3136308715950998022 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59_value:
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
    m_data: [41, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value:
    LeanStringObject<16> = LeanStringObject {
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
        100, 117, 109, 109, 121, 71, 101, 116, 67, 111, 110, 102, 105, 103, 63, 0,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value
        ) as *mut LeanObject,
        6345706506204061227 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value:
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
    m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_2:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value
        ) as *mut LeanObject,
        9368229134555052249 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value:
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
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65_value:
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
    m_data: [46, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 108, 97, 98, 71, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0_value) as *mut LeanObject,1504741952025245079 as *mut LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(
    mut v_opts_1086_: *mut LeanObject,
    mut v_opt_1087_: *mut LeanObject,
) -> u8 {
    let mut v_name_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    v_name_1088_ = lean_ctor_get(v_opt_1087_, 0);
    v_defValue_1089_ = lean_ctor_get(v_opt_1087_, 1);
    v_map_1090_ = lean_ctor_get(v_opts_1086_, 0);
    v___x_1091_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1090_,
            v_name_1088_,
        );
    if lean_obj_tag(v___x_1091_) == 0 {
        let mut v___x_1092_: u8 = 0;
        v___x_1092_ = (lean_unbox(v_defValue_1089_) as u8);
        return v___x_1092_;
    } else {
        let mut v_val_1093_: *mut LeanObject = core::ptr::null_mut();
        v_val_1093_ = lean_ctor_get(v___x_1091_, 0);
        lean_inc(v_val_1093_);
        lean_dec_ref_known(v___x_1091_, 1);
        if lean_obj_tag(v_val_1093_) == 1 {
            let mut v_v_1094_: u8 = 0;
            v_v_1094_ = lean_ctor_get_uint8(v_val_1093_, 0 as u32);
            lean_dec_ref_known(v_val_1093_, 0);
            return v_v_1094_;
        } else {
            let mut v___x_1095_: u8 = 0;
            lean_dec(v_val_1093_);
            v___x_1095_ = (lean_unbox(v_defValue_1089_) as u8);
            return v___x_1095_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5___boxed(
    mut v_opts_1096_: *mut LeanObject,
    mut v_opt_1097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1098_: u8 = 0;
    let mut v_r_1099_: *mut LeanObject = core::ptr::null_mut();
    v_res_1098_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(v_opts_1096_, v_opt_1097_);
    lean_dec_ref(v_opt_1097_);
    lean_dec_ref(v_opts_1096_);
    v_r_1099_ = lean_box((v_res_1098_) as usize);
    return v_r_1099_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0()
-> *mut LeanObject {
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    v___x_1100_ = lean_box(1);
    v___x_1101_ = l_Lean_MessageData_ofFormat(v___x_1100_);
    return v___x_1101_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3()
-> *mut LeanObject {
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2;
    v___x_1106_ = l_Lean_MessageData_ofFormat(v___x_1105_);
    return v___x_1106_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6(
    mut v_x_1107_: *mut LeanObject,
    mut v_x_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1113_: u8 = 0;
    let mut v_before_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut v_unused_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1108_) == 0 {
                    return v_x_1107_;
                } else {
                    v_head_1109_ = lean_ctor_get(v_x_1108_, 0);
                    v_tail_1110_ = lean_ctor_get(v_x_1108_, 1);
                    v_isSharedCheck_1132_ = (!lean_is_exclusive(v_x_1108_)) as u8;
                    if v_isSharedCheck_1132_ == 0 {
                        v___x_1112_ = v_x_1108_;
                        v_isShared_1113_ = v_isSharedCheck_1132_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1110_);
                        lean_inc(v_head_1109_);
                        lean_dec(v_x_1108_);
                        v___x_1112_ = lean_box(0);
                        v_isShared_1113_ = v_isSharedCheck_1132_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1114_ = lean_ctor_get(v_head_1109_, 0);
                v_isSharedCheck_1130_ = (!lean_is_exclusive(v_head_1109_)) as u8;
                if v_isSharedCheck_1130_ == 0 {
                    v_unused_1131_ = lean_ctor_get(v_head_1109_, 1);
                    lean_dec(v_unused_1131_);
                    v___x_1116_ = v_head_1109_;
                    v_isShared_1117_ = v_isSharedCheck_1130_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_1114_);
                    lean_dec(v_head_1109_);
                    v___x_1116_ = lean_box(0);
                    v_isShared_1117_ = v_isSharedCheck_1130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1118_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0);
                if v_isShared_1117_ == 0 {
                    lean_ctor_set_tag(v___x_1116_, 7);
                    lean_ctor_set(v___x_1116_, 1, v___x_1118_);
                    lean_ctor_set(v___x_1116_, 0, v_x_1107_);
                    v___x_1120_ = v___x_1116_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_x_1107_);
                    lean_ctor_set(v_reuseFailAlloc_1129_, 1, v___x_1118_);
                    v___x_1120_ = v_reuseFailAlloc_1129_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1121_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3);
                if v_isShared_1113_ == 0 {
                    lean_ctor_set_tag(v___x_1112_, 7);
                    lean_ctor_set(v___x_1112_, 1, v___x_1121_);
                    lean_ctor_set(v___x_1112_, 0, v___x_1120_);
                    v___x_1123_ = v___x_1112_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1128_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1120_);
                    lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1121_);
                    v___x_1123_ = v_reuseFailAlloc_1128_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1124_ = l_Lean_MessageData_ofSyntax(v_before_1114_);
                v___x_1125_ = l_Lean_indentD(v___x_1124_);
                v___x_1126_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1126_, 0, v___x_1123_);
                lean_ctor_set(v___x_1126_, 1, v___x_1125_);
                v_x_1107_ = v___x_1126_;
                v_x_1108_ = v_tail_1110_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    v___x_1136_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1;
    v___x_1137_ = l_Lean_MessageData_ofFormat(v___x_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(
    mut v_msgData_1138_: *mut LeanObject,
    mut v_macroStack_1139_: *mut LeanObject,
    mut v___y_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: u8 = 0;
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut v_unused_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1142_ = lean_ctor_get(v___y_1140_, 2);
                v___x_1143_ = l_Lean_Elab_pp_macroStack;
                v___x_1144_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(v_options_1142_, v___x_1143_);
                if v___x_1144_ == 0 {
                    lean_dec(v_macroStack_1139_);
                    v___x_1145_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1145_, 0, v_msgData_1138_);
                    return v___x_1145_;
                } else {
                    if lean_obj_tag(v_macroStack_1139_) == 0 {
                        v___x_1146_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1146_, 0, v_msgData_1138_);
                        return v___x_1146_;
                    } else {
                        v_head_1147_ = lean_ctor_get(v_macroStack_1139_, 0);
                        lean_inc(v_head_1147_);
                        v_after_1148_ = lean_ctor_get(v_head_1147_, 1);
                        v_isSharedCheck_1163_ = (!lean_is_exclusive(v_head_1147_)) as u8;
                        if v_isSharedCheck_1163_ == 0 {
                            v_unused_1164_ = lean_ctor_get(v_head_1147_, 0);
                            lean_dec(v_unused_1164_);
                            v___x_1150_ = v_head_1147_;
                            v_isShared_1151_ = v_isSharedCheck_1163_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_1148_);
                            lean_dec(v_head_1147_);
                            v___x_1150_ = lean_box(0);
                            v_isShared_1151_ = v_isSharedCheck_1163_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1152_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0);
                if v_isShared_1151_ == 0 {
                    lean_ctor_set_tag(v___x_1150_, 7);
                    lean_ctor_set(v___x_1150_, 1, v___x_1152_);
                    lean_ctor_set(v___x_1150_, 0, v_msgData_1138_);
                    v___x_1154_ = v___x_1150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_msgData_1138_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1152_);
                    v___x_1154_ = v_reuseFailAlloc_1162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1155_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2);
                v___x_1156_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1156_, 0, v___x_1154_);
                lean_ctor_set(v___x_1156_, 1, v___x_1155_);
                v___x_1157_ = l_Lean_MessageData_ofSyntax(v_after_1148_);
                v___x_1158_ = l_Lean_indentD(v___x_1157_);
                v_msgData_1159_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_1159_, 0, v___x_1156_);
                lean_ctor_set(v_msgData_1159_, 1, v___x_1158_);
                v___x_1160_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6(v_msgData_1159_, v_macroStack_1139_);
                v___x_1161_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1161_, 0, v___x_1160_);
                return v___x_1161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___boxed(
    mut v_msgData_1165_: *mut LeanObject,
    mut v_macroStack_1166_: *mut LeanObject,
    mut v___y_1167_: *mut LeanObject,
    mut v___y_1168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1169_: *mut LeanObject = core::ptr::null_mut();
    v_res_1169_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_msgData_1165_, v_macroStack_1166_, v___y_1167_);
    lean_dec_ref(v___y_1167_);
    return v_res_1169_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(
    mut v_msgData_1170_: *mut LeanObject,
    mut v___y_1171_: *mut LeanObject,
    mut v___y_1172_: *mut LeanObject,
    mut v___y_1173_: *mut LeanObject,
    mut v___y_1174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    v___x_1176_ = lean_st_ref_get(v___y_1174_);
    v_env_1177_ = lean_ctor_get(v___x_1176_, 0);
    lean_inc_ref(v_env_1177_);
    lean_dec(v___x_1176_);
    v___x_1178_ = lean_st_ref_get(v___y_1172_);
    v_mctx_1179_ = lean_ctor_get(v___x_1178_, 0);
    lean_inc_ref(v_mctx_1179_);
    lean_dec(v___x_1178_);
    v_lctx_1180_ = lean_ctor_get(v___y_1171_, 2);
    v_options_1181_ = lean_ctor_get(v___y_1173_, 2);
    lean_inc_ref(v_options_1181_);
    lean_inc_ref(v_lctx_1180_);
    v___x_1182_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1182_, 0, v_env_1177_);
    lean_ctor_set(v___x_1182_, 1, v_mctx_1179_);
    lean_ctor_set(v___x_1182_, 2, v_lctx_1180_);
    lean_ctor_set(v___x_1182_, 3, v_options_1181_);
    v___x_1183_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1183_, 0, v___x_1182_);
    lean_ctor_set(v___x_1183_, 1, v_msgData_1170_);
    v___x_1184_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1184_, 0, v___x_1183_);
    return v___x_1184_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2___boxed(
    mut v_msgData_1185_: *mut LeanObject,
    mut v___y_1186_: *mut LeanObject,
    mut v___y_1187_: *mut LeanObject,
    mut v___y_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
    mut v___y_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1191_: *mut LeanObject = core::ptr::null_mut();
    v_res_1191_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(v_msgData_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
    lean_dec(v___y_1189_);
    lean_dec_ref(v___y_1188_);
    lean_dec(v___y_1187_);
    lean_dec_ref(v___y_1186_);
    return v_res_1191_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(
    mut v_msg_1192_: *mut LeanObject,
    mut v___y_1193_: *mut LeanObject,
    mut v___y_1194_: *mut LeanObject,
    mut v___y_1195_: *mut LeanObject,
    mut v___y_1196_: *mut LeanObject,
    mut v___y_1197_: *mut LeanObject,
    mut v___y_1198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1200_ = lean_ctor_get(v___y_1197_, 5);
                v___x_1201_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(v_msg_1192_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
                v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
                lean_inc(v_a_1202_);
                lean_dec_ref(v___x_1201_);
                v_macroStack_1203_ = lean_ctor_get(v___y_1193_, 1);
                v___x_1204_ = l_Lean_Elab_getBetterRef(v_ref_1200_, v_macroStack_1203_);
                lean_inc(v_macroStack_1203_);
                v___x_1205_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_a_1202_, v_macroStack_1203_, v___y_1197_);
                v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
                v_isSharedCheck_1214_ = (!lean_is_exclusive(v___x_1205_)) as u8;
                if v_isSharedCheck_1214_ == 0 {
                    v___x_1208_ = v___x_1205_;
                    v_isShared_1209_ = v_isSharedCheck_1214_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1206_);
                    lean_dec(v___x_1205_);
                    v___x_1208_ = lean_box(0);
                    v_isShared_1209_ = v_isSharedCheck_1214_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1210_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1210_, 0, v___x_1204_);
                lean_ctor_set(v___x_1210_, 1, v_a_1206_);
                if v_isShared_1209_ == 0 {
                    lean_ctor_set_tag(v___x_1208_, 1);
                    lean_ctor_set(v___x_1208_, 0, v___x_1210_);
                    v___x_1212_ = v___x_1208_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
                    v___x_1212_ = v_reuseFailAlloc_1213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg___boxed(
    mut v_msg_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
    mut v___y_1218_: *mut LeanObject,
    mut v___y_1219_: *mut LeanObject,
    mut v___y_1220_: *mut LeanObject,
    mut v___y_1221_: *mut LeanObject,
    mut v___y_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1223_: *mut LeanObject = core::ptr::null_mut();
    v_res_1223_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v_msg_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
    lean_dec(v___y_1221_);
    lean_dec_ref(v___y_1220_);
    lean_dec(v___y_1219_);
    lean_dec_ref(v___y_1218_);
    lean_dec(v___y_1217_);
    lean_dec_ref(v___y_1216_);
    return v_res_1223_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0(
    mut v_stx_1224_: *mut LeanObject,
    mut v_output_1225_: *mut LeanObject,
    mut v_trees_1226_: *mut LeanObject,
    mut v___y_1227_: *mut LeanObject,
    mut v___y_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
    mut v___y_1231_: *mut LeanObject,
    mut v___y_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    v_lctx_1234_ = lean_ctor_get(v___y_1229_, 2);
    lean_inc_ref(v_lctx_1234_);
    v___x_1235_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1235_, 0, v_lctx_1234_);
    lean_ctor_set(v___x_1235_, 1, v_stx_1224_);
    lean_ctor_set(v___x_1235_, 2, v_output_1225_);
    v___x_1236_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_1236_, 0, v___x_1235_);
    v___x_1237_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1237_, 0, v___x_1236_);
    lean_ctor_set(v___x_1237_, 1, v_trees_1226_);
    v___x_1238_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_stx_1239_: *mut LeanObject,
    mut v_output_1240_: *mut LeanObject,
    mut v_trees_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1249_: *mut LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0(v_stx_1239_, v_output_1240_, v_trees_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
    lean_dec(v___y_1247_);
    lean_dec_ref(v___y_1246_);
    lean_dec(v___y_1245_);
    lean_dec_ref(v___y_1244_);
    lean_dec(v___y_1243_);
    lean_dec_ref(v___y_1242_);
    return v_res_1249_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    v___x_1250_ = lean_unsigned_to_nat(32);
    v___x_1251_ = lean_mk_empty_array_with_capacity(v___x_1250_);
    v___x_1252_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1252_, 0, v___x_1251_);
    return v___x_1252_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1253_: usize = 0;
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    v___x_1253_ = 5usize;
    v___x_1254_ = lean_unsigned_to_nat(0);
    v___x_1255_ = lean_unsigned_to_nat(32);
    v___x_1256_ = lean_mk_empty_array_with_capacity(v___x_1255_);
    v___x_1257_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
    v___x_1258_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1258_, 0, v___x_1257_);
    lean_ctor_set(v___x_1258_, 1, v___x_1256_);
    lean_ctor_set(v___x_1258_, 2, v___x_1254_);
    lean_ctor_set(v___x_1258_, 3, v___x_1254_);
    lean_ctor_set_usize(v___x_1258_, 4, v___x_1253_);
    return v___x_1258_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v___y_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v_enabled_1277_: u8 = 0;
    let mut v_assignment_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut v_unused_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1261_ = lean_st_ref_get(v___y_1259_);
                v_infoState_1262_ = lean_ctor_get(v___x_1261_, 7);
                lean_inc_ref(v_infoState_1262_);
                lean_dec(v___x_1261_);
                v_trees_1263_ = lean_ctor_get(v_infoState_1262_, 2);
                lean_inc_ref(v_trees_1263_);
                lean_dec_ref(v_infoState_1262_);
                v___x_1264_ = lean_st_ref_take(v___y_1259_);
                v_infoState_1265_ = lean_ctor_get(v___x_1264_, 7);
                v_env_1266_ = lean_ctor_get(v___x_1264_, 0);
                v_nextMacroScope_1267_ = lean_ctor_get(v___x_1264_, 1);
                v_ngen_1268_ = lean_ctor_get(v___x_1264_, 2);
                v_auxDeclNGen_1269_ = lean_ctor_get(v___x_1264_, 3);
                v_traceState_1270_ = lean_ctor_get(v___x_1264_, 4);
                v_cache_1271_ = lean_ctor_get(v___x_1264_, 5);
                v_messages_1272_ = lean_ctor_get(v___x_1264_, 6);
                v_snapshotTasks_1273_ = lean_ctor_get(v___x_1264_, 8);
                v_isSharedCheck_1294_ = (!lean_is_exclusive(v___x_1264_)) as u8;
                if v_isSharedCheck_1294_ == 0 {
                    v___x_1275_ = v___x_1264_;
                    v_isShared_1276_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1273_);
                    lean_inc(v_infoState_1265_);
                    lean_inc(v_messages_1272_);
                    lean_inc(v_cache_1271_);
                    lean_inc(v_traceState_1270_);
                    lean_inc(v_auxDeclNGen_1269_);
                    lean_inc(v_ngen_1268_);
                    lean_inc(v_nextMacroScope_1267_);
                    lean_inc(v_env_1266_);
                    lean_dec(v___x_1264_);
                    v___x_1275_ = lean_box(0);
                    v_isShared_1276_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1277_ = lean_ctor_get_uint8(
                    v_infoState_1265_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_1278_ = lean_ctor_get(v_infoState_1265_, 0);
                v_lazyAssignment_1279_ = lean_ctor_get(v_infoState_1265_, 1);
                v_isSharedCheck_1292_ = (!lean_is_exclusive(v_infoState_1265_)) as u8;
                if v_isSharedCheck_1292_ == 0 {
                    v_unused_1293_ = lean_ctor_get(v_infoState_1265_, 2);
                    lean_dec(v_unused_1293_);
                    v___x_1281_ = v_infoState_1265_;
                    v_isShared_1282_ = v_isSharedCheck_1292_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_1279_);
                    lean_inc(v_assignment_1278_);
                    lean_dec(v_infoState_1265_);
                    v___x_1281_ = lean_box(0);
                    v_isShared_1282_ = v_isSharedCheck_1292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1283_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
                if v_isShared_1282_ == 0 {
                    lean_ctor_set(v___x_1281_, 2, v___x_1283_);
                    v___x_1285_ = v___x_1281_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_assignment_1278_);
                    lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_lazyAssignment_1279_);
                    lean_ctor_set(v_reuseFailAlloc_1291_, 2, v___x_1283_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1291_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_1277_,
                    );
                    v___x_1285_ = v_reuseFailAlloc_1291_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1276_ == 0 {
                    lean_ctor_set(v___x_1275_, 7, v___x_1285_);
                    v___x_1287_ = v___x_1275_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_env_1266_);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_nextMacroScope_1267_);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_ngen_1268_);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 3, v_auxDeclNGen_1269_);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 4, v_traceState_1270_);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 5, v_cache_1271_);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 6, v_messages_1272_);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 7, v___x_1285_);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 8, v_snapshotTasks_1273_);
                    v___x_1287_ = v_reuseFailAlloc_1290_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1288_ = lean_st_ref_set(v___y_1259_, v___x_1287_);
                v___x_1289_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1289_, 0, v_trees_1263_);
                return v___x_1289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v___y_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1297_: *mut LeanObject = core::ptr::null_mut();
    v_res_1297_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1295_);
    lean_dec(v___y_1295_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(
    mut v___y_1298_: *mut LeanObject,
    mut v_mkInfoTree_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
    mut v_a_1305_: *mut LeanObject,
    mut v_a_x3f_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1328_: u8 = 0;
    let mut v_enabled_1329_: u8 = 0;
    let mut v_assignment_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1347_: u8 = 0;
    let mut v_unused_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1349_: u8 = 0;
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut v_a_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1354_: u8 = 0;
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1308_ = lean_st_ref_get(v___y_1298_);
                v_infoState_1309_ = lean_ctor_get(v___x_1308_, 7);
                lean_inc_ref(v_infoState_1309_);
                lean_dec(v___x_1308_);
                v_trees_1310_ = lean_ctor_get(v_infoState_1309_, 2);
                lean_inc_ref(v_trees_1310_);
                lean_dec_ref(v_infoState_1309_);
                lean_inc(v___y_1298_);
                lean_inc_ref(v___y_1304_);
                lean_inc(v___y_1303_);
                lean_inc_ref(v___y_1302_);
                lean_inc(v___y_1301_);
                lean_inc_ref(v___y_1300_);
                v___x_1311_ = lean_apply_8(
                    v_mkInfoTree_1299_,
                    v_trees_1310_,
                    v___y_1300_,
                    v___y_1301_,
                    v___y_1302_,
                    v___y_1303_,
                    v___y_1304_,
                    v___y_1298_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1311_) == 0 {
                    v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
                    v_isSharedCheck_1350_ = (!lean_is_exclusive(v___x_1311_)) as u8;
                    if v_isSharedCheck_1350_ == 0 {
                        v___x_1314_ = v___x_1311_;
                        v_isShared_1315_ = v_isSharedCheck_1350_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1312_);
                        lean_dec(v___x_1311_);
                        v___x_1314_ = lean_box(0);
                        v_isShared_1315_ = v_isSharedCheck_1350_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_1305_);
                    v_a_1351_ = lean_ctor_get(v___x_1311_, 0);
                    v_isSharedCheck_1358_ = (!lean_is_exclusive(v___x_1311_)) as u8;
                    if v_isSharedCheck_1358_ == 0 {
                        v___x_1353_ = v___x_1311_;
                        v_isShared_1354_ = v_isSharedCheck_1358_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1351_);
                        lean_dec(v___x_1311_);
                        v___x_1353_ = lean_box(0);
                        v_isShared_1354_ = v_isSharedCheck_1358_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1316_ = lean_st_ref_take(v___y_1298_);
                v_infoState_1317_ = lean_ctor_get(v___x_1316_, 7);
                v_env_1318_ = lean_ctor_get(v___x_1316_, 0);
                v_nextMacroScope_1319_ = lean_ctor_get(v___x_1316_, 1);
                v_ngen_1320_ = lean_ctor_get(v___x_1316_, 2);
                v_auxDeclNGen_1321_ = lean_ctor_get(v___x_1316_, 3);
                v_traceState_1322_ = lean_ctor_get(v___x_1316_, 4);
                v_cache_1323_ = lean_ctor_get(v___x_1316_, 5);
                v_messages_1324_ = lean_ctor_get(v___x_1316_, 6);
                v_snapshotTasks_1325_ = lean_ctor_get(v___x_1316_, 8);
                v_isSharedCheck_1349_ = (!lean_is_exclusive(v___x_1316_)) as u8;
                if v_isSharedCheck_1349_ == 0 {
                    v___x_1327_ = v___x_1316_;
                    v_isShared_1328_ = v_isSharedCheck_1349_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1325_);
                    lean_inc(v_infoState_1317_);
                    lean_inc(v_messages_1324_);
                    lean_inc(v_cache_1323_);
                    lean_inc(v_traceState_1322_);
                    lean_inc(v_auxDeclNGen_1321_);
                    lean_inc(v_ngen_1320_);
                    lean_inc(v_nextMacroScope_1319_);
                    lean_inc(v_env_1318_);
                    lean_dec(v___x_1316_);
                    v___x_1327_ = lean_box(0);
                    v_isShared_1328_ = v_isSharedCheck_1349_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_1329_ = lean_ctor_get_uint8(
                    v_infoState_1317_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_1330_ = lean_ctor_get(v_infoState_1317_, 0);
                v_lazyAssignment_1331_ = lean_ctor_get(v_infoState_1317_, 1);
                v_isSharedCheck_1347_ = (!lean_is_exclusive(v_infoState_1317_)) as u8;
                if v_isSharedCheck_1347_ == 0 {
                    v_unused_1348_ = lean_ctor_get(v_infoState_1317_, 2);
                    lean_dec(v_unused_1348_);
                    v___x_1333_ = v_infoState_1317_;
                    v_isShared_1334_ = v_isSharedCheck_1347_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_1331_);
                    lean_inc(v_assignment_1330_);
                    lean_dec(v_infoState_1317_);
                    v___x_1333_ = lean_box(0);
                    v_isShared_1334_ = v_isSharedCheck_1347_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1335_ = l_Lean_PersistentArray_push___redArg(v_a_1305_, v_a_1312_);
                if v_isShared_1334_ == 0 {
                    lean_ctor_set(v___x_1333_, 2, v___x_1335_);
                    v___x_1337_ = v___x_1333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_assignment_1330_);
                    lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_lazyAssignment_1331_);
                    lean_ctor_set(v_reuseFailAlloc_1346_, 2, v___x_1335_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1346_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_1329_,
                    );
                    v___x_1337_ = v_reuseFailAlloc_1346_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1328_ == 0 {
                    lean_ctor_set(v___x_1327_, 7, v___x_1337_);
                    v___x_1339_ = v___x_1327_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_env_1318_);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_nextMacroScope_1319_);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_ngen_1320_);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 3, v_auxDeclNGen_1321_);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 4, v_traceState_1322_);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 5, v_cache_1323_);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 6, v_messages_1324_);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 7, v___x_1337_);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 8, v_snapshotTasks_1325_);
                    v___x_1339_ = v_reuseFailAlloc_1345_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1340_ = lean_st_ref_set(v___y_1298_, v___x_1339_);
                v___x_1341_ = lean_box(0);
                if v_isShared_1315_ == 0 {
                    lean_ctor_set(v___x_1314_, 0, v___x_1341_);
                    v___x_1343_ = v___x_1314_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
                    v___x_1343_ = v_reuseFailAlloc_1344_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1343_;
            }
            7 => {
                if v_isShared_1354_ == 0 {
                    v___x_1356_ = v___x_1353_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
                    v___x_1356_ = v_reuseFailAlloc_1357_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0___boxed(
    mut v___y_1359_: *mut LeanObject,
    mut v_mkInfoTree_1360_: *mut LeanObject,
    mut v___y_1361_: *mut LeanObject,
    mut v___y_1362_: *mut LeanObject,
    mut v___y_1363_: *mut LeanObject,
    mut v___y_1364_: *mut LeanObject,
    mut v___y_1365_: *mut LeanObject,
    mut v_a_1366_: *mut LeanObject,
    mut v_a_x3f_1367_: *mut LeanObject,
    mut v___y_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1369_: *mut LeanObject = core::ptr::null_mut();
    v_res_1369_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_1359_, v_mkInfoTree_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v_a_1366_, v_a_x3f_1367_);
    lean_dec(v_a_x3f_1367_);
    lean_dec_ref(v___y_1365_);
    lean_dec(v___y_1364_);
    lean_dec_ref(v___y_1363_);
    lean_dec(v___y_1362_);
    lean_dec_ref(v___y_1361_);
    lean_dec(v___y_1359_);
    return v_res_1369_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(
    mut v_x_1370_: *mut LeanObject,
    mut v_mkInfoTree_1371_: *mut LeanObject,
    mut v___y_1372_: *mut LeanObject,
    mut v___y_1373_: *mut LeanObject,
    mut v___y_1374_: *mut LeanObject,
    mut v___y_1375_: *mut LeanObject,
    mut v___y_1376_: *mut LeanObject,
    mut v___y_1377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_1381_: u8 = 0;
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1389_: u8 = 0;
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1395_: u8 = 0;
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1399_: u8 = 0;
    let mut v_unused_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1408_: u8 = 0;
    let mut v_reuseFailAlloc_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut v_a_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_unused_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1425_: u8 = 0;
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1379_ = lean_st_ref_get(v___y_1377_);
                v_infoState_1380_ = lean_ctor_get(v___x_1379_, 7);
                lean_inc_ref(v_infoState_1380_);
                lean_dec(v___x_1379_);
                v_enabled_1381_ = lean_ctor_get_uint8(
                    v_infoState_1380_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_1380_);
                if v_enabled_1381_ == 0 {
                    lean_dec_ref(v_mkInfoTree_1371_);
                    lean_inc(v___y_1377_);
                    lean_inc_ref(v___y_1376_);
                    lean_inc(v___y_1375_);
                    lean_inc_ref(v___y_1374_);
                    lean_inc(v___y_1373_);
                    lean_inc_ref(v___y_1372_);
                    v___x_1382_ = lean_apply_7(
                        v_x_1370_,
                        v___y_1372_,
                        v___y_1373_,
                        v___y_1374_,
                        v___y_1375_,
                        v___y_1376_,
                        v___y_1377_,
                        lean_box(0),
                    );
                    return v___x_1382_;
                } else {
                    v___x_1383_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1377_);
                    v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
                    lean_inc(v_a_1384_);
                    lean_dec_ref(v___x_1383_);
                    lean_inc(v___y_1377_);
                    lean_inc_ref(v___y_1376_);
                    lean_inc(v___y_1375_);
                    lean_inc_ref(v___y_1374_);
                    lean_inc(v___y_1373_);
                    lean_inc_ref(v___y_1372_);
                    v_r_1385_ = lean_apply_7(
                        v_x_1370_,
                        v___y_1372_,
                        v___y_1373_,
                        v___y_1374_,
                        v___y_1375_,
                        v___y_1376_,
                        v___y_1377_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_1385_) == 0 {
                        v_a_1386_ = lean_ctor_get(v_r_1385_, 0);
                        v_isSharedCheck_1410_ = (!lean_is_exclusive(v_r_1385_)) as u8;
                        if v_isSharedCheck_1410_ == 0 {
                            v___x_1388_ = v_r_1385_;
                            v_isShared_1389_ = v_isSharedCheck_1410_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1386_);
                            lean_dec(v_r_1385_);
                            v___x_1388_ = lean_box(0);
                            v_isShared_1389_ = v_isSharedCheck_1410_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1411_ = lean_ctor_get(v_r_1385_, 0);
                        lean_inc(v_a_1411_);
                        lean_dec_ref_known(v_r_1385_, 1);
                        v___x_1412_ = lean_box(0);
                        v___x_1413_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_1377_, v_mkInfoTree_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v_a_1384_, v___x_1412_);
                        if lean_obj_tag(v___x_1413_) == 0 {
                            v_isSharedCheck_1420_ = (!lean_is_exclusive(v___x_1413_)) as u8;
                            if v_isSharedCheck_1420_ == 0 {
                                v_unused_1421_ = lean_ctor_get(v___x_1413_, 0);
                                lean_dec(v_unused_1421_);
                                v___x_1415_ = v___x_1413_;
                                v_isShared_1416_ = v_isSharedCheck_1420_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_1413_);
                                v___x_1415_ = lean_box(0);
                                v_isShared_1416_ = v_isSharedCheck_1420_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1411_);
                            v_a_1422_ = lean_ctor_get(v___x_1413_, 0);
                            v_isSharedCheck_1429_ = (!lean_is_exclusive(v___x_1413_)) as u8;
                            if v_isSharedCheck_1429_ == 0 {
                                v___x_1424_ = v___x_1413_;
                                v_isShared_1425_ = v_isSharedCheck_1429_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_1422_);
                                lean_dec(v___x_1413_);
                                v___x_1424_ = lean_box(0);
                                v_isShared_1425_ = v_isSharedCheck_1429_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_1386_);
                if v_isShared_1389_ == 0 {
                    lean_ctor_set_tag(v___x_1388_, 1);
                    v___x_1391_ = v___x_1388_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1386_);
                    v___x_1391_ = v_reuseFailAlloc_1409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1392_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_1377_, v_mkInfoTree_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v_a_1384_, v___x_1391_);
                lean_dec_ref(v___x_1391_);
                if lean_obj_tag(v___x_1392_) == 0 {
                    v_isSharedCheck_1399_ = (!lean_is_exclusive(v___x_1392_)) as u8;
                    if v_isSharedCheck_1399_ == 0 {
                        v_unused_1400_ = lean_ctor_get(v___x_1392_, 0);
                        lean_dec(v_unused_1400_);
                        v___x_1394_ = v___x_1392_;
                        v_isShared_1395_ = v_isSharedCheck_1399_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_1392_);
                        v___x_1394_ = lean_box(0);
                        v_isShared_1395_ = v_isSharedCheck_1399_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1386_);
                    v_a_1401_ = lean_ctor_get(v___x_1392_, 0);
                    v_isSharedCheck_1408_ = (!lean_is_exclusive(v___x_1392_)) as u8;
                    if v_isSharedCheck_1408_ == 0 {
                        v___x_1403_ = v___x_1392_;
                        v_isShared_1404_ = v_isSharedCheck_1408_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1401_);
                        lean_dec(v___x_1392_);
                        v___x_1403_ = lean_box(0);
                        v_isShared_1404_ = v_isSharedCheck_1408_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1395_ == 0 {
                    lean_ctor_set(v___x_1394_, 0, v_a_1386_);
                    v___x_1397_ = v___x_1394_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1386_);
                    v___x_1397_ = v_reuseFailAlloc_1398_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1397_;
            }
            5 => {
                if v_isShared_1404_ == 0 {
                    v___x_1406_ = v___x_1403_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
                    v___x_1406_ = v_reuseFailAlloc_1407_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1406_;
            }
            7 => {
                if v_isShared_1416_ == 0 {
                    lean_ctor_set_tag(v___x_1415_, 1);
                    lean_ctor_set(v___x_1415_, 0, v_a_1411_);
                    v___x_1418_ = v___x_1415_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1411_);
                    v___x_1418_ = v_reuseFailAlloc_1419_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1418_;
            }
            9 => {
                if v_isShared_1425_ == 0 {
                    v___x_1427_ = v___x_1424_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
                    v___x_1427_ = v_reuseFailAlloc_1428_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_1430_: *mut LeanObject,
    mut v_mkInfoTree_1431_: *mut LeanObject,
    mut v___y_1432_: *mut LeanObject,
    mut v___y_1433_: *mut LeanObject,
    mut v___y_1434_: *mut LeanObject,
    mut v___y_1435_: *mut LeanObject,
    mut v___y_1436_: *mut LeanObject,
    mut v___y_1437_: *mut LeanObject,
    mut v___y_1438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1439_: *mut LeanObject = core::ptr::null_mut();
    v_res_1439_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_1430_, v_mkInfoTree_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
    lean_dec(v___y_1437_);
    lean_dec_ref(v___y_1436_);
    lean_dec(v___y_1435_);
    lean_dec_ref(v___y_1434_);
    lean_dec(v___y_1433_);
    lean_dec_ref(v___y_1432_);
    return v_res_1439_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(
    mut v_stx_1440_: *mut LeanObject,
    mut v_output_1441_: *mut LeanObject,
    mut v_x_1442_: *mut LeanObject,
    mut v___y_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
    mut v___y_1446_: *mut LeanObject,
    mut v___y_1447_: *mut LeanObject,
    mut v___y_1448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    v___f_1450_ = lean_alloc_closure(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
    lean_closure_set(v___f_1450_, 0, v_stx_1440_);
    lean_closure_set(v___f_1450_, 1, v_output_1441_);
    v___x_1451_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_1442_, v___f_1450_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
    return v___x_1451_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___boxed(
    mut v_stx_1452_: *mut LeanObject,
    mut v_output_1453_: *mut LeanObject,
    mut v_x_1454_: *mut LeanObject,
    mut v___y_1455_: *mut LeanObject,
    mut v___y_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
    mut v___y_1460_: *mut LeanObject,
    mut v___y_1461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1462_: *mut LeanObject = core::ptr::null_mut();
    v_res_1462_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_stx_1452_, v_output_1453_, v_x_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
    lean_dec(v___y_1460_);
    lean_dec_ref(v___y_1459_);
    lean_dec(v___y_1458_);
    lean_dec_ref(v___y_1457_);
    lean_dec(v___y_1456_);
    lean_dec_ref(v___y_1455_);
    return v_res_1462_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(
    mut v_beforeStx_1463_: *mut LeanObject,
    mut v_afterStx_1464_: *mut LeanObject,
    mut v_x_1465_: *mut LeanObject,
    mut v___y_1466_: *mut LeanObject,
    mut v___y_1467_: *mut LeanObject,
    mut v___y_1468_: *mut LeanObject,
    mut v___y_1469_: *mut LeanObject,
    mut v___y_1470_: *mut LeanObject,
    mut v___y_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1482_: u8 = 0;
    let mut v_a_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1486_: u8 = 0;
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_afterStx_1464_);
                lean_inc(v_beforeStx_1463_);
                v___x_1473_ = lean_alloc_closure(
                    l_Lean_Elab_Term_withPushMacroExpansionStack___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                lean_closure_set(v___x_1473_, 0, lean_box(0));
                lean_closure_set(v___x_1473_, 1, v_beforeStx_1463_);
                lean_closure_set(v___x_1473_, 2, v_afterStx_1464_);
                lean_closure_set(v___x_1473_, 3, v_x_1465_);
                v___x_1474_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_beforeStx_1463_, v_afterStx_1464_, v___x_1473_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
                if lean_obj_tag(v___x_1474_) == 0 {
                    v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
                    v_isSharedCheck_1482_ = (!lean_is_exclusive(v___x_1474_)) as u8;
                    if v_isSharedCheck_1482_ == 0 {
                        v___x_1477_ = v___x_1474_;
                        v_isShared_1478_ = v_isSharedCheck_1482_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1475_);
                        lean_dec(v___x_1474_);
                        v___x_1477_ = lean_box(0);
                        v_isShared_1478_ = v_isSharedCheck_1482_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1483_ = lean_ctor_get(v___x_1474_, 0);
                    v_isSharedCheck_1490_ = (!lean_is_exclusive(v___x_1474_)) as u8;
                    if v_isSharedCheck_1490_ == 0 {
                        v___x_1485_ = v___x_1474_;
                        v_isShared_1486_ = v_isSharedCheck_1490_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1483_);
                        lean_dec(v___x_1474_);
                        v___x_1485_ = lean_box(0);
                        v_isShared_1486_ = v_isSharedCheck_1490_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1478_ == 0 {
                    v___x_1480_ = v___x_1477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
                    v___x_1480_ = v_reuseFailAlloc_1481_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1480_;
            }
            3 => {
                if v_isShared_1486_ == 0 {
                    v___x_1488_ = v___x_1485_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
                    v___x_1488_ = v_reuseFailAlloc_1489_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1488_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg___boxed(
    mut v_beforeStx_1491_: *mut LeanObject,
    mut v_afterStx_1492_: *mut LeanObject,
    mut v_x_1493_: *mut LeanObject,
    mut v___y_1494_: *mut LeanObject,
    mut v___y_1495_: *mut LeanObject,
    mut v___y_1496_: *mut LeanObject,
    mut v___y_1497_: *mut LeanObject,
    mut v___y_1498_: *mut LeanObject,
    mut v___y_1499_: *mut LeanObject,
    mut v___y_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1501_: *mut LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_beforeStx_1491_, v_afterStx_1492_, v_x_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
    lean_dec(v___y_1499_);
    lean_dec_ref(v___y_1498_);
    lean_dec(v___y_1497_);
    lean_dec_ref(v___y_1496_);
    lean_dec(v___y_1495_);
    lean_dec_ref(v___y_1494_);
    return v_res_1501_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6()
-> *mut LeanObject {
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    v___x_1513_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5;
    v___x_1514_ = l_Lake_DSL_packageDeclName;
    v___x_1515_ = l_Lean_Name_str___override(v___x_1514_, v___x_1513_);
    return v___x_1515_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7()
-> *mut LeanObject {
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    v___x_1516_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6),
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6_once
        ),
        _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6,
    );
    v___x_1517_ = lean_mk_syntax_ident(v___x_1516_);
    return v___x_1517_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9()
-> *mut LeanObject {
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    v___x_1519_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8;
    v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(
    mut v_stx_1521_: *mut LeanObject,
    mut v_expectedType_x3f_1522_: *mut LeanObject,
    mut v_a_1523_: *mut LeanObject,
    mut v_a_1524_: *mut LeanObject,
    mut v_a_1525_: *mut LeanObject,
    mut v_a_1526_: *mut LeanObject,
    mut v_a_1527_: *mut LeanObject,
    mut v_a_1528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1581_: u8 = 0;
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1553_ = lean_st_ref_get(v_a_1528_);
                v_env_1554_ = lean_ctor_get(v___x_1553_, 0);
                lean_inc_ref_n(v_env_1554_, 2);
                lean_dec(v___x_1553_);
                v___x_1555_ = lean_box(0);
                v___x_1556_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4;
                v___x_1573_ = l_Lake_DSL_packageDeclName;
                v___x_1574_ = 1;
                v___x_1575_ = l_Lean_Environment_contains(v_env_1554_, v___x_1573_, v___x_1574_);
                if v___x_1575_ == 0 {
                    lean_dec_ref(v_env_1554_);
                    lean_dec(v_expectedType_x3f_1522_);
                    lean_dec(v_stx_1521_);
                    v___x_1576_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9_once
                        ),
                        _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9,
                    );
                    v___x_1577_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v___x_1576_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
                    v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
                    v_isSharedCheck_1585_ = (!lean_is_exclusive(v___x_1577_)) as u8;
                    if v_isSharedCheck_1585_ == 0 {
                        v___x_1580_ = v___x_1577_;
                        v_isShared_1581_ = v_isSharedCheck_1585_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1578_);
                        lean_dec(v___x_1577_);
                        v___x_1580_ = lean_box(0);
                        v_isShared_1581_ = v_isSharedCheck_1585_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_1558_ = v_a_1523_;
                    v___y_1559_ = v_a_1524_;
                    v___y_1560_ = v_a_1525_;
                    v___y_1561_ = v_a_1526_;
                    v___y_1562_ = v_a_1527_;
                    v___y_1563_ = v_a_1528_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1539_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3;
                v___x_1540_ = l_Nat_reprFast(v___y_1532_);
                v___x_1541_ = lean_box(2);
                v___x_1542_ = l_Lean_Syntax_mkNumLit(v___x_1540_, v___x_1541_);
                v___x_1543_ = lean_unsigned_to_nat(2);
                v___x_1544_ = lean_mk_empty_array_with_capacity(v___x_1543_);
                v___x_1545_ = lean_array_push(v___x_1544_, v___y_1538_);
                v___x_1546_ = lean_array_push(v___x_1545_, v___x_1542_);
                v___x_1547_ = l_Lean_Syntax_mkCApp(v___x_1539_, v___x_1546_);
                v___x_1548_ = 1;
                v___x_1549_ = lean_box((v___x_1548_) as usize);
                v___x_1550_ = lean_box((v___x_1548_) as usize);
                lean_inc(v___x_1547_);
                v___x_1551_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTerm___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                lean_closure_set(v___x_1551_, 0, v___x_1547_);
                lean_closure_set(v___x_1551_, 1, v_expectedType_x3f_1522_);
                lean_closure_set(v___x_1551_, 2, v___x_1549_);
                lean_closure_set(v___x_1551_, 3, v___x_1550_);
                v___x_1552_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_1521_, v___x_1547_, v___x_1551_, v___y_1533_, v___y_1536_, v___y_1535_, v___y_1537_, v___y_1534_, v___y_1531_);
                return v___x_1552_;
            }
            2 => {
                v___x_1564_ = l_Lake_nameExt;
                v_asyncMode_1565_ = lean_ctor_get(v___x_1564_, 2);
                v___x_1566_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1556_,
                        v___x_1564_,
                        v_env_1554_,
                        v_asyncMode_1565_,
                        v___x_1555_,
                    );
                v_snd_1567_ = lean_ctor_get(v___x_1566_, 1);
                lean_inc(v_snd_1567_);
                if lean_obj_tag(v_snd_1567_) == 0 {
                    v_fst_1568_ = lean_ctor_get(v___x_1566_, 0);
                    lean_inc(v_fst_1568_);
                    lean_dec(v___x_1566_);
                    v___x_1569_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7_once
                        ),
                        _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7,
                    );
                    v___y_1531_ = v___y_1563_;
                    v___y_1532_ = v_fst_1568_;
                    v___y_1533_ = v___y_1558_;
                    v___y_1534_ = v___y_1562_;
                    v___y_1535_ = v___y_1560_;
                    v___y_1536_ = v___y_1559_;
                    v___y_1537_ = v___y_1561_;
                    v___y_1538_ = v___x_1569_;
                    state = 1;
                    continue;
                } else {
                    v_fst_1570_ = lean_ctor_get(v___x_1566_, 0);
                    lean_inc(v_fst_1570_);
                    lean_dec(v___x_1566_);
                    v___x_1571_ = 0;
                    lean_inc(v_stx_1521_);
                    v___x_1572_ = l_Lake_Name_quoteFrom(v_stx_1521_, v_snd_1567_, v___x_1571_);
                    v___y_1531_ = v___y_1563_;
                    v___y_1532_ = v_fst_1570_;
                    v___y_1533_ = v___y_1558_;
                    v___y_1534_ = v___y_1562_;
                    v___y_1535_ = v___y_1560_;
                    v___y_1536_ = v___y_1559_;
                    v___y_1537_ = v___y_1561_;
                    v___y_1538_ = v___x_1572_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_1581_ == 0 {
                    v___x_1583_ = v___x_1580_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
                    v___x_1583_ = v_reuseFailAlloc_1584_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed(
    mut v_stx_1586_: *mut LeanObject,
    mut v_expectedType_x3f_1587_: *mut LeanObject,
    mut v_a_1588_: *mut LeanObject,
    mut v_a_1589_: *mut LeanObject,
    mut v_a_1590_: *mut LeanObject,
    mut v_a_1591_: *mut LeanObject,
    mut v_a_1592_: *mut LeanObject,
    mut v_a_1593_: *mut LeanObject,
    mut v_a_1594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1595_: *mut LeanObject = core::ptr::null_mut();
    v_res_1595_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(
        v_stx_1586_,
        v_expectedType_x3f_1587_,
        v_a_1588_,
        v_a_1589_,
        v_a_1590_,
        v_a_1591_,
        v_a_1592_,
        v_a_1593_,
    );
    lean_dec(v_a_1593_);
    lean_dec_ref(v_a_1592_);
    lean_dec(v_a_1591_);
    lean_dec_ref(v_a_1590_);
    lean_dec(v_a_1589_);
    lean_dec_ref(v_a_1588_);
    return v_res_1595_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(
    mut v_00_u03b1_1596_: *mut LeanObject,
    mut v_beforeStx_1597_: *mut LeanObject,
    mut v_afterStx_1598_: *mut LeanObject,
    mut v_x_1599_: *mut LeanObject,
    mut v___y_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    v___x_1607_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_beforeStx_1597_, v_afterStx_1598_, v_x_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
    return v___x_1607_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___boxed(
    mut v_00_u03b1_1608_: *mut LeanObject,
    mut v_beforeStx_1609_: *mut LeanObject,
    mut v_afterStx_1610_: *mut LeanObject,
    mut v_x_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
    mut v___y_1617_: *mut LeanObject,
    mut v___y_1618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1619_: *mut LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(v_00_u03b1_1608_, v_beforeStx_1609_, v_afterStx_1610_, v_x_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
    lean_dec(v___y_1617_);
    lean_dec_ref(v___y_1616_);
    lean_dec(v___y_1615_);
    lean_dec_ref(v___y_1614_);
    lean_dec(v___y_1613_);
    lean_dec_ref(v___y_1612_);
    return v_res_1619_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(
    mut v_00_u03b1_1620_: *mut LeanObject,
    mut v_msg_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
    mut v___y_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v_msg_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
    return v___x_1629_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___boxed(
    mut v_00_u03b1_1630_: *mut LeanObject,
    mut v_msg_1631_: *mut LeanObject,
    mut v___y_1632_: *mut LeanObject,
    mut v___y_1633_: *mut LeanObject,
    mut v___y_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
    mut v___y_1637_: *mut LeanObject,
    mut v___y_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1639_: *mut LeanObject = core::ptr::null_mut();
    v_res_1639_ =
        l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(
            v_00_u03b1_1630_,
            v_msg_1631_,
            v___y_1632_,
            v___y_1633_,
            v___y_1634_,
            v___y_1635_,
            v___y_1636_,
            v___y_1637_,
        );
    lean_dec(v___y_1637_);
    lean_dec_ref(v___y_1636_);
    lean_dec(v___y_1635_);
    lean_dec_ref(v___y_1634_);
    lean_dec(v___y_1633_);
    lean_dec_ref(v___y_1632_);
    return v_res_1639_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(
    mut v_00_u03b1_1640_: *mut LeanObject,
    mut v_stx_1641_: *mut LeanObject,
    mut v_output_1642_: *mut LeanObject,
    mut v_x_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
    mut v___y_1645_: *mut LeanObject,
    mut v___y_1646_: *mut LeanObject,
    mut v___y_1647_: *mut LeanObject,
    mut v___y_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_stx_1641_, v_output_1642_, v_x_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___boxed(
    mut v_00_u03b1_1652_: *mut LeanObject,
    mut v_stx_1653_: *mut LeanObject,
    mut v_output_1654_: *mut LeanObject,
    mut v_x_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
    mut v___y_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1663_: *mut LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(v_00_u03b1_1652_, v_stx_1653_, v_output_1654_, v_x_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
    lean_dec(v___y_1661_);
    lean_dec_ref(v___y_1660_);
    lean_dec(v___y_1659_);
    lean_dec_ref(v___y_1658_);
    lean_dec(v___y_1657_);
    lean_dec_ref(v___y_1656_);
    return v_res_1663_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(
    mut v_msgData_1664_: *mut LeanObject,
    mut v_macroStack_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_msgData_1664_, v_macroStack_1665_, v___y_1670_);
    return v___x_1673_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___boxed(
    mut v_msgData_1674_: *mut LeanObject,
    mut v_macroStack_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1683_: *mut LeanObject = core::ptr::null_mut();
    v_res_1683_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(v_msgData_1674_, v_macroStack_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
    lean_dec(v___y_1681_);
    lean_dec_ref(v___y_1680_);
    lean_dec(v___y_1679_);
    lean_dec_ref(v___y_1678_);
    lean_dec(v___y_1677_);
    lean_dec_ref(v___y_1676_);
    return v_res_1683_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4(
    mut v___y_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1689_);
    return v___x_1691_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v___y_1692_: *mut LeanObject,
    mut v___y_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1699_: *mut LeanObject = core::ptr::null_mut();
    v_res_1699_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4(v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
    lean_dec(v___y_1697_);
    lean_dec_ref(v___y_1696_);
    lean_dec(v___y_1695_);
    lean_dec_ref(v___y_1694_);
    lean_dec(v___y_1693_);
    lean_dec_ref(v___y_1692_);
    return v_res_1699_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1700_: *mut LeanObject,
    mut v_x_1701_: *mut LeanObject,
    mut v_mkInfoTree_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    v___x_1710_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_1701_, v_mkInfoTree_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
    return v___x_1710_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1711_: *mut LeanObject,
    mut v_x_1712_: *mut LeanObject,
    mut v_mkInfoTree_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1721_: *mut LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1(v_00_u03b1_1711_, v_x_1712_, v_mkInfoTree_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
    lean_dec(v___y_1719_);
    lean_dec_ref(v___y_1718_);
    lean_dec(v___y_1717_);
    lean_dec_ref(v___y_1716_);
    lean_dec(v___y_1715_);
    lean_dec_ref(v___y_1714_);
    return v_res_1721_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1()
-> *mut LeanObject {
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    v___x_1757_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_1758_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3;
    v___x_1759_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14;
    v___x_1760_ = lean_alloc_closure(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_1761_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1757_,
        v___x_1758_,
        v___x_1759_,
        v___x_1760_,
    );
    return v___x_1761_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___boxed(
    mut v_a_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1763_: *mut LeanObject = core::ptr::null_mut();
    v_res_1763_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1();
    return v_res_1763_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(
    mut v_stx_1781_: *mut LeanObject,
    mut v_expectedType_x3f_1782_: *mut LeanObject,
    mut v_a_1783_: *mut LeanObject,
    mut v_a_1784_: *mut LeanObject,
    mut v_a_1785_: *mut LeanObject,
    mut v_a_1786_: *mut LeanObject,
    mut v_a_1787_: *mut LeanObject,
    mut v_a_1788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1790_ = lean_st_ref_get(v_a_1788_);
                v_env_1798_ = lean_ctor_get(v___x_1790_, 0);
                lean_inc_ref(v_env_1798_);
                lean_dec(v___x_1790_);
                v___x_1799_ = l_Lake_dirExt;
                v_asyncMode_1800_ = lean_ctor_get(v___x_1799_, 2);
                v___x_1801_ = lean_box(0);
                v___x_1802_ = lean_box(0);
                v___x_1803_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1801_,
                        v___x_1799_,
                        v_env_1798_,
                        v_asyncMode_1800_,
                        v___x_1802_,
                    );
                if lean_obj_tag(v___x_1803_) == 1 {
                    v_val_1804_ = lean_ctor_get(v___x_1803_, 0);
                    lean_inc(v_val_1804_);
                    lean_dec_ref_known(v___x_1803_, 1);
                    v___x_1805_ = 0;
                    v___x_1806_ = l_Lean_SourceInfo_fromRef(v_stx_1781_, v___x_1805_);
                    v___x_1807_ = l_Lean_Syntax_mkStrLit(v_val_1804_, v___x_1806_);
                    v___x_1808_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3;
                    v___x_1809_ = l_Lean_mkCIdentFrom(v_stx_1781_, v___x_1808_, v___x_1805_);
                    v___x_1810_ = lean_unsigned_to_nat(1);
                    v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
                    v___x_1812_ = lean_array_push(v___x_1811_, v___x_1807_);
                    v___x_1813_ = l_Lean_Syntax_mkApp(v___x_1809_, v___x_1812_);
                    v___y_1792_ = v___x_1813_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_1803_);
                    v___x_1814_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5;
                    v___x_1815_ = 0;
                    v___x_1816_ = l_Lean_mkCIdentFrom(v_stx_1781_, v___x_1814_, v___x_1815_);
                    v___x_1817_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7;
                    v___x_1818_ = l_Lean_mkCIdentFrom(v_stx_1781_, v___x_1817_, v___x_1815_);
                    v___x_1819_ = lean_unsigned_to_nat(1);
                    v___x_1820_ = lean_mk_empty_array_with_capacity(v___x_1819_);
                    v___x_1821_ = lean_array_push(v___x_1820_, v___x_1818_);
                    v___x_1822_ = l_Lean_Syntax_mkApp(v___x_1816_, v___x_1821_);
                    v___y_1792_ = v___x_1822_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1793_ = 1;
                v___x_1794_ = lean_box((v___x_1793_) as usize);
                v___x_1795_ = lean_box((v___x_1793_) as usize);
                lean_inc(v___y_1792_);
                v___x_1796_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTerm___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                lean_closure_set(v___x_1796_, 0, v___y_1792_);
                lean_closure_set(v___x_1796_, 1, v_expectedType_x3f_1782_);
                lean_closure_set(v___x_1796_, 2, v___x_1794_);
                lean_closure_set(v___x_1796_, 3, v___x_1795_);
                v___x_1797_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_1781_, v___y_1792_, v___x_1796_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
                return v___x_1797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed(
    mut v_stx_1823_: *mut LeanObject,
    mut v_expectedType_x3f_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
    mut v_a_1828_: *mut LeanObject,
    mut v_a_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
    mut v_a_1831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1832_: *mut LeanObject = core::ptr::null_mut();
    v_res_1832_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(
        v_stx_1823_,
        v_expectedType_x3f_1824_,
        v_a_1825_,
        v_a_1826_,
        v_a_1827_,
        v_a_1828_,
        v_a_1829_,
        v_a_1830_,
    );
    lean_dec(v_a_1830_);
    lean_dec_ref(v_a_1829_);
    lean_dec(v_a_1828_);
    lean_dec_ref(v_a_1827_);
    lean_dec(v_a_1826_);
    lean_dec_ref(v_a_1825_);
    return v_res_1832_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1()
-> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_1844_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1;
    v___x_1845_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3;
    v___x_1846_ = lean_alloc_closure(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_1847_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1843_,
        v___x_1844_,
        v___x_1845_,
        v___x_1846_,
    );
    return v___x_1847_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___boxed(
    mut v_a_1848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1849_: *mut LeanObject = core::ptr::null_mut();
    v_res_1849_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1();
    return v_res_1849_;
}
pub unsafe fn l_Lake_DSL_dummyGetConfig_x3f(mut v_a_1850_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    v___x_1851_ = lean_box(0);
    return v___x_1851_;
}
pub unsafe fn l_Lake_DSL_dummyGetConfig_x3f___boxed(
    mut v_a_1852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1853_: *mut LeanObject = core::ptr::null_mut();
    v_res_1853_ = l_Lake_DSL_dummyGetConfig_x3f(v_a_1852_);
    lean_dec(v_a_1852_);
    return v_res_1853_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    v___x_1854_ = lean_box(0);
    v___x_1855_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1856_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1856_, 0, v___x_1855_);
    lean_ctor_set(v___x_1856_, 1, v___x_1854_);
    return v___x_1856_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    v___x_1858_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0);
    v___x_1859_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1859_, 0, v___x_1858_);
    return v___x_1859_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___boxed(
    mut v___y_1860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1861_: *mut LeanObject = core::ptr::null_mut();
    v_res_1861_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
    return v_res_1861_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(
    mut v_00_u03b1_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
    return v___x_1870_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___boxed(
    mut v_00_u03b1_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
    mut v___y_1873_: *mut LeanObject,
    mut v___y_1874_: *mut LeanObject,
    mut v___y_1875_: *mut LeanObject,
    mut v___y_1876_: *mut LeanObject,
    mut v___y_1877_: *mut LeanObject,
    mut v___y_1878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1879_: *mut LeanObject = core::ptr::null_mut();
    v_res_1879_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(v_00_u03b1_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
    lean_dec(v___y_1877_);
    lean_dec_ref(v___y_1876_);
    lean_dec(v___y_1875_);
    lean_dec_ref(v___y_1874_);
    lean_dec(v___y_1873_);
    lean_dec_ref(v___y_1872_);
    return v_res_1879_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7()
-> *mut LeanObject {
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    v___x_1894_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6;
    v___x_1895_ = l_String_toRawSubstring_x27(v___x_1894_);
    return v___x_1895_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22()
-> *mut LeanObject {
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lake_DSL_dummyDir___closed__0;
    v___x_1928_ = l_String_toRawSubstring_x27(v___x_1927_);
    return v___x_1928_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37()
-> *mut LeanObject {
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    v___x_1963_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36;
    v___x_1964_ = l_String_toRawSubstring_x27(v___x_1963_);
    return v___x_1964_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43()
-> *mut LeanObject {
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    v___x_1977_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9;
    v___x_1978_ = l_String_toRawSubstring_x27(v___x_1977_);
    return v___x_1978_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53()
-> *mut LeanObject {
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    v___x_2001_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52;
    v___x_2002_ = l_String_toRawSubstring_x27(v___x_2001_);
    return v___x_2002_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(
    mut v_stx_2030_: *mut LeanObject,
    mut v_expectedType_x3f_2031_: *mut LeanObject,
    mut v_a_2032_: *mut LeanObject,
    mut v_a_2033_: *mut LeanObject,
    mut v_a_2034_: *mut LeanObject,
    mut v_a_2035_: *mut LeanObject,
    mut v_a_2036_: *mut LeanObject,
    mut v_a_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: u8 = 0;
    let mut v_a_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: u8 = 0;
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: u8 = 0;
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2148_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_expectedType_x3f_2031_);
                v___x_2039_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(
                    v_expectedType_x3f_2031_,
                    v_a_2032_,
                    v_a_2033_,
                    v_a_2034_,
                    v_a_2035_,
                    v_a_2036_,
                    v_a_2037_,
                );
                if lean_obj_tag(v___x_2039_) == 0 {
                    lean_dec_ref_known(v___x_2039_, 1);
                    v___x_2040_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1;
                    lean_inc(v_stx_2030_);
                    v___x_2041_ = l_Lean_Syntax_isOfKind(v_stx_2030_, v___x_2040_);
                    if v___x_2041_ == 0 {
                        lean_dec(v_expectedType_x3f_2031_);
                        lean_dec(v_stx_2030_);
                        v___x_2048_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
                        return v___x_2048_;
                    } else {
                        v___x_2049_ = lean_st_ref_get(v_a_2037_);
                        v_env_2050_ = lean_ctor_get(v___x_2049_, 0);
                        lean_inc_ref(v_env_2050_);
                        lean_dec(v___x_2049_);
                        v___x_2051_ = l_Lake_optsExt;
                        v_asyncMode_2052_ = lean_ctor_get(v___x_2051_, 2);
                        v___x_2053_ = lean_unsigned_to_nat(1);
                        v___x_2054_ = l_Lean_Syntax_getArg(v_stx_2030_, v___x_2053_);
                        v___x_2055_ = lean_box(0);
                        v___x_2056_ = lean_box(0);
                        v___x_2057_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2055_, v___x_2051_, v_env_2050_, v_asyncMode_2052_, v___x_2056_);
                        if lean_obj_tag(v___x_2057_) == 1 {
                            v_val_2058_ = lean_ctor_get(v___x_2057_, 0);
                            lean_inc(v_val_2058_);
                            lean_dec_ref_known(v___x_2057_, 1);
                            v___x_2059_ = l_Lean_TSyntax_getId(v___x_2054_);
                            lean_dec(v___x_2054_);
                            v___x_2060_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_2058_, v___x_2059_);
                            lean_dec(v___x_2059_);
                            lean_dec(v_val_2058_);
                            if lean_obj_tag(v___x_2060_) == 1 {
                                v_val_2061_ = lean_ctor_get(v___x_2060_, 0);
                                lean_inc(v_val_2061_);
                                lean_dec_ref_known(v___x_2060_, 1);
                                v_ref_2062_ = lean_ctor_get(v_a_2036_, 5);
                                v_quotContext_2063_ = lean_ctor_get(v_a_2036_, 10);
                                v_currMacroScope_2064_ = lean_ctor_get(v_a_2036_, 11);
                                v___x_2065_ = 0;
                                v___x_2066_ = l_Lean_SourceInfo_fromRef(v_ref_2062_, v___x_2065_);
                                v___x_2067_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5;
                                v___x_2068_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7), core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7_once), _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7);
                                v___x_2069_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8;
                                lean_inc(v_currMacroScope_2064_);
                                lean_inc(v_quotContext_2063_);
                                v___x_2070_ = l_Lean_addMacroScope(
                                    v_quotContext_2063_,
                                    v___x_2069_,
                                    v_currMacroScope_2064_,
                                );
                                v___x_2071_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12;
                                lean_inc_n(v___x_2066_, 3);
                                v___x_2072_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_2072_, 0, v___x_2066_);
                                lean_ctor_set(v___x_2072_, 1, v___x_2068_);
                                lean_ctor_set(v___x_2072_, 2, v___x_2070_);
                                lean_ctor_set(v___x_2072_, 3, v___x_2071_);
                                v___x_2073_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14;
                                v___x_2074_ = l_Lean_Syntax_mkStrLit(v_val_2061_, v___x_2066_);
                                v___x_2075_ =
                                    l_Lean_Syntax_node1(v___x_2066_, v___x_2073_, v___x_2074_);
                                v___x_2076_ = l_Lean_Syntax_node2(
                                    v___x_2066_,
                                    v___x_2067_,
                                    v___x_2072_,
                                    v___x_2075_,
                                );
                                v_a_2043_ = v___x_2076_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_2060_);
                                v_ref_2077_ = lean_ctor_get(v_a_2036_, 5);
                                v_quotContext_2078_ = lean_ctor_get(v_a_2036_, 10);
                                v_currMacroScope_2079_ = lean_ctor_get(v_a_2036_, 11);
                                v___x_2080_ = 0;
                                v___x_2081_ = l_Lean_SourceInfo_fromRef(v_ref_2077_, v___x_2080_);
                                v___x_2082_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16;
                                v___x_2083_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18;
                                v___x_2084_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19;
                                lean_inc_n(v___x_2081_, 12);
                                v___x_2085_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_2085_, 0, v___x_2081_);
                                lean_ctor_set(v___x_2085_, 1, v___x_2084_);
                                v___x_2086_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21;
                                v___x_2087_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22), core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22_once), _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22);
                                lean_inc_n(v_currMacroScope_2079_, 4);
                                lean_inc_n(v_quotContext_2078_, 4);
                                v___x_2088_ = l_Lean_addMacroScope(
                                    v_quotContext_2078_,
                                    v___x_2056_,
                                    v_currMacroScope_2079_,
                                );
                                v___x_2089_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35;
                                v___x_2090_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_2090_, 0, v___x_2081_);
                                lean_ctor_set(v___x_2090_, 1, v___x_2087_);
                                lean_ctor_set(v___x_2090_, 2, v___x_2088_);
                                lean_ctor_set(v___x_2090_, 3, v___x_2089_);
                                v___x_2091_ =
                                    l_Lean_Syntax_node1(v___x_2081_, v___x_2086_, v___x_2090_);
                                v___x_2092_ = l_Lean_Syntax_node2(
                                    v___x_2081_,
                                    v___x_2083_,
                                    v___x_2085_,
                                    v___x_2091_,
                                );
                                v___x_2093_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37), core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37_once), _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37);
                                v___x_2094_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38;
                                v___x_2095_ = l_Lean_addMacroScope(
                                    v_quotContext_2078_,
                                    v___x_2094_,
                                    v_currMacroScope_2079_,
                                );
                                v___x_2096_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41;
                                v___x_2097_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_2097_, 0, v___x_2081_);
                                lean_ctor_set(v___x_2097_, 1, v___x_2093_);
                                lean_ctor_set(v___x_2097_, 2, v___x_2095_);
                                lean_ctor_set(v___x_2097_, 3, v___x_2096_);
                                v___x_2098_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42;
                                v___x_2099_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_2099_, 0, v___x_2081_);
                                lean_ctor_set(v___x_2099_, 1, v___x_2098_);
                                v___x_2100_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14;
                                v___x_2101_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5;
                                v___x_2102_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43), core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43_once), _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43);
                                v___x_2103_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44;
                                v___x_2104_ = l_Lean_addMacroScope(
                                    v_quotContext_2078_,
                                    v___x_2103_,
                                    v_currMacroScope_2079_,
                                );
                                v___x_2105_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51;
                                v___x_2106_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_2106_, 0, v___x_2081_);
                                lean_ctor_set(v___x_2106_, 1, v___x_2102_);
                                lean_ctor_set(v___x_2106_, 2, v___x_2104_);
                                lean_ctor_set(v___x_2106_, 3, v___x_2105_);
                                v___x_2107_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53), core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53_once), _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53);
                                v___x_2108_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54;
                                v___x_2109_ = l_Lean_addMacroScope(
                                    v_quotContext_2078_,
                                    v___x_2108_,
                                    v_currMacroScope_2079_,
                                );
                                v___x_2110_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58;
                                v___x_2111_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_2111_, 0, v___x_2081_);
                                lean_ctor_set(v___x_2111_, 1, v___x_2107_);
                                lean_ctor_set(v___x_2111_, 2, v___x_2109_);
                                lean_ctor_set(v___x_2111_, 3, v___x_2110_);
                                v___x_2112_ =
                                    l_Lean_Syntax_node1(v___x_2081_, v___x_2100_, v___x_2111_);
                                v___x_2113_ = l_Lean_Syntax_node2(
                                    v___x_2081_,
                                    v___x_2101_,
                                    v___x_2106_,
                                    v___x_2112_,
                                );
                                v___x_2114_ =
                                    l_Lean_Syntax_node1(v___x_2081_, v___x_2100_, v___x_2113_);
                                v___x_2115_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59;
                                v___x_2116_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_2116_, 0, v___x_2081_);
                                lean_ctor_set(v___x_2116_, 1, v___x_2115_);
                                v___x_2117_ = l_Lean_Syntax_node5(
                                    v___x_2081_,
                                    v___x_2082_,
                                    v___x_2092_,
                                    v___x_2097_,
                                    v___x_2099_,
                                    v___x_2114_,
                                    v___x_2116_,
                                );
                                v_a_2043_ = v___x_2117_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_2057_);
                            v___x_2118_ =
                                l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61;
                            v___x_2119_ = 0;
                            v___x_2120_ =
                                l_Lean_mkCIdentFrom(v_stx_2030_, v___x_2118_, v___x_2119_);
                            v___x_2126_ = l_Lean_TSyntax_getId(v___x_2054_);
                            lean_dec(v___x_2054_);
                            v___x_2127_ = lean_box(0);
                            lean_inc(v___x_2126_);
                            v___x_2128_ =
                                l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                    v___x_2127_,
                                    v___x_2126_,
                                );
                            if lean_obj_tag(v___x_2128_) == 0 {
                                v___x_2129_ = l_Lean_quoteNameMk(v___x_2126_);
                                v___y_2122_ = v___x_2129_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_2126_);
                                v_val_2130_ = lean_ctor_get(v___x_2128_, 0);
                                lean_inc(v_val_2130_);
                                lean_dec_ref_known(v___x_2128_, 1);
                                v___x_2131_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63;
                                v___x_2132_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64;
                                v___x_2133_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65;
                                v___x_2134_ = lean_string_intercalate(v___x_2133_, v_val_2130_);
                                v___x_2135_ = lean_string_append(v___x_2132_, v___x_2134_);
                                lean_dec_ref(v___x_2134_);
                                v___x_2136_ = lean_box(2);
                                v___x_2137_ = l_Lean_Syntax_mkNameLit(v___x_2135_, v___x_2136_);
                                v___x_2138_ = lean_mk_empty_array_with_capacity(v___x_2053_);
                                v___x_2139_ = lean_array_push(v___x_2138_, v___x_2137_);
                                v___x_2140_ = lean_alloc_ctor(1, 3, (0) as u32);
                                lean_ctor_set(v___x_2140_, 0, v___x_2136_);
                                lean_ctor_set(v___x_2140_, 1, v___x_2131_);
                                lean_ctor_set(v___x_2140_, 2, v___x_2139_);
                                v___y_2122_ = v___x_2140_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_expectedType_x3f_2031_);
                    lean_dec(v_stx_2030_);
                    v_a_2141_ = lean_ctor_get(v___x_2039_, 0);
                    v_isSharedCheck_2148_ = (!lean_is_exclusive(v___x_2039_)) as u8;
                    if v_isSharedCheck_2148_ == 0 {
                        v___x_2143_ = v___x_2039_;
                        v_isShared_2144_ = v_isSharedCheck_2148_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2141_);
                        lean_dec(v___x_2039_);
                        v___x_2143_ = lean_box(0);
                        v_isShared_2144_ = v_isSharedCheck_2148_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2044_ = lean_box((v___x_2041_) as usize);
                v___x_2045_ = lean_box((v___x_2041_) as usize);
                lean_inc(v_a_2043_);
                v___x_2046_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTerm___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                lean_closure_set(v___x_2046_, 0, v_a_2043_);
                lean_closure_set(v___x_2046_, 1, v_expectedType_x3f_2031_);
                lean_closure_set(v___x_2046_, 2, v___x_2044_);
                lean_closure_set(v___x_2046_, 3, v___x_2045_);
                v___x_2047_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_2030_, v_a_2043_, v___x_2046_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
                return v___x_2047_;
            }
            2 => {
                v___x_2123_ = lean_mk_empty_array_with_capacity(v___x_2053_);
                v___x_2124_ = lean_array_push(v___x_2123_, v___y_2122_);
                v___x_2125_ = l_Lean_Syntax_mkApp(v___x_2120_, v___x_2124_);
                v_a_2043_ = v___x_2125_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_2144_ == 0 {
                    v___x_2146_ = v___x_2143_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
                    v___x_2146_ = v_reuseFailAlloc_2147_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed(
    mut v_stx_2149_: *mut LeanObject,
    mut v_expectedType_x3f_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
    mut v_a_2152_: *mut LeanObject,
    mut v_a_2153_: *mut LeanObject,
    mut v_a_2154_: *mut LeanObject,
    mut v_a_2155_: *mut LeanObject,
    mut v_a_2156_: *mut LeanObject,
    mut v_a_2157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2158_: *mut LeanObject = core::ptr::null_mut();
    v_res_2158_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(
        v_stx_2149_,
        v_expectedType_x3f_2150_,
        v_a_2151_,
        v_a_2152_,
        v_a_2153_,
        v_a_2154_,
        v_a_2155_,
        v_a_2156_,
    );
    lean_dec(v_a_2156_);
    lean_dec_ref(v_a_2155_);
    lean_dec(v_a_2154_);
    lean_dec_ref(v_a_2153_);
    lean_dec(v_a_2152_);
    lean_dec_ref(v_a_2151_);
    return v_res_2158_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1()
-> *mut LeanObject {
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    v___x_2164_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_2165_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1;
    v___x_2166_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1;
    v___x_2167_ = lean_alloc_closure(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2168_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2164_,
        v___x_2165_,
        v___x_2166_,
        v___x_2167_,
    );
    return v___x_2168_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___boxed(
    mut v_a_2169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2170_: *mut LeanObject = core::ptr::null_mut();
    v_res_2170_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1();
    return v_res_2170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Extensions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_DSL_Extensions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_DSL_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_DSL_Config(builtin);
}

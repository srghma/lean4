// Lean compiler output
// Module: Lean.Elab.Do.PatternVar
// Imports: Lean.Elab.Term Lean.Parser.Do Lean.Elab.PatternVar Lean.Elab.Quotation
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Meta::Defs::{l_Lean_HygieneInfo_mkIdent, l_Lean_Syntax_isNone};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isIdent, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::PatternVar::{
    initialize_Lean_Elab_PatternVar, l_Lean_Elab_Term_getPatternVars,
    l_Lean_Elab_Term_getPatternsVars, runtime_initialize_Lean_Elab_PatternVar,
};
use crate::r#gen::Lean::Elab::Quotation::Util::{
    l_Lean_Elab_Term_Quotation_getPatternVars, l_Lean_Elab_Term_Quotation_getPatternsVars,
};
use crate::r#gen::Lean::Elab::Quotation::{
    initialize_Lean_Elab_Quotation, runtime_initialize_Lean_Elab_Quotation,
};
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Parser::Do::{
    initialize_Lean_Parser_Do, runtime_initialize_Lean_Parser_Do,
};
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::ffi::lean_st_ref_get;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__3_value:
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
    m_data: [108, 101, 116, 73, 100, 0],
};
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_0:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__3_value) as *mut crate::leanh::LeanObject,13708106407786339395 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__5_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [78, 111, 116, 32, 97, 32, 108, 101, 116, 73, 100, 58, 32, 0],
};
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 111, 108, 101, 0],
};
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_0:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9_value:
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
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11_value
        ) as *mut crate::leanh::LeanObject,
        9871775667037945883 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 104, 105, 115, 0],
};
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__14_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        10861733237677782054 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_getLetDeclVars___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [108, 101, 116, 68, 101, 99, 108, 0],
    };
static mut l_Lean_Elab_Do_getLetDeclVars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value
            ) as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value
            ) as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_getLetDeclVars___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8036185514257755965 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_getLetDeclVars___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_getLetDeclVars___closed__2_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            78, 111, 116, 32, 97, 32, 108, 101, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105,
            111, 110, 58, 32, 0,
        ],
    };
static mut l_Lean_Elab_Do_getLetDeclVars___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Do_getLetDeclVars___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_getLetDeclVars___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_getLetDeclVars___closed__4_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0],
    };
static mut l_Lean_Elab_Do_getLetDeclVars___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value
            ) as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value
            ) as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_getLetDeclVars___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__4_value)
                as *mut crate::leanh::LeanObject,
            17116161260408496210 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_getLetDeclVars___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_getLetDeclVars___closed__6_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [108, 101, 116, 80, 97, 116, 68, 101, 99, 108, 0],
    };
static mut l_Lean_Elab_Do_getLetDeclVars___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value
            ) as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value
            ) as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_getLetDeclVars___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17263257370765302025 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_getLetDeclVars___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_getLetDeclVars___closed__8_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [108, 101, 116, 69, 113, 110, 115, 68, 101, 99, 108, 0],
    };
static mut l_Lean_Elab_Do_getLetDeclVars___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value
            ) as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value
            ) as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_getLetDeclVars___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__8_value)
                as *mut crate::leanh::LeanObject,
            6781002338968064594 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_getLetDeclVars___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetDeclVars___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 101, 116, 82, 101, 99, 68, 101, 99, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,13733354118357790922 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_getLetRecDeclsVars___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [108, 101, 116, 82, 101, 99, 68, 101, 99, 108, 115, 0],
    };
static mut l_Lean_Elab_Do_getLetRecDeclsVars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetRecDeclsVars___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value
            ) as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value
            ) as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_getLetRecDeclsVars___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9139758955001836903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_getLetRecDeclsVars___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_getLetRecDeclsVars___closed__2_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Do_getLetRecDeclsVars___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getLetRecDeclsVars___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [109, 97, 116, 99, 104, 69, 120, 112, 114, 80, 97, 116, 0],
};
static mut l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_0:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2538307196702464034 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Do_getPatternVarsEx(
    mut v_pattern_861_: *mut crate::leanh::LeanObject,
    mut v_a_862_: *mut crate::leanh::LeanObject,
    mut v_a_863_: *mut crate::leanh::LeanObject,
    mut v_a_864_: *mut crate::leanh::LeanObject,
    mut v_a_865_: *mut crate::leanh::LeanObject,
    mut v_a_866_: *mut crate::leanh::LeanObject,
    mut v_a_867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_874_: u8 = 0;
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_878_: u8 = 0;
    let mut v_a_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_882_: u8 = 0;
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_892_: u8 = 0;
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_898_: u8 = 0;
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_902_: u8 = 0;
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: u8 = 0;
    let mut v_a_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_908_: u8 = 0;
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_887_ = l_Lean_Meta_saveState___redArg(v_a_865_, v_a_867_);
                if crate::leanh::lean_obj_tag(v___x_887_) == 0 {
                    v_a_888_ = crate::leanh::lean_ctor_get(v___x_887_, 0);
                    crate::leanh::lean_inc(v_a_888_);
                    crate::leanh::lean_dec_ref_known(v___x_887_, 1);
                    crate::leanh::lean_inc(v_pattern_861_);
                    v___x_889_ = l_Lean_Elab_Term_Quotation_getPatternVars(
                        v_pattern_861_,
                        v_a_862_,
                        v_a_863_,
                        v_a_864_,
                        v_a_865_,
                        v_a_866_,
                        v_a_867_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_889_) == 0 {
                        crate::leanh::lean_dec(v_a_888_);
                        crate::leanh::lean_dec(v_pattern_861_);
                        v___y_870_ = v___x_889_;
                        state = 1;
                        continue;
                    } else {
                        v_a_890_ = crate::leanh::lean_ctor_get(v___x_889_, 0);
                        crate::leanh::lean_inc(v_a_890_);
                        v___x_903_ = l_Lean_Exception_isInterrupt(v_a_890_);
                        if v___x_903_ == 0 {
                            v___x_904_ = l_Lean_Exception_isRuntime(v_a_890_);
                            v___y_892_ = v___x_904_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_890_);
                            v___y_892_ = v___x_903_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_pattern_861_);
                    v_a_905_ = crate::leanh::lean_ctor_get(v___x_887_, 0);
                    v_isSharedCheck_912_ = (!crate::leanh::lean_is_exclusive(v___x_887_)) as u8;
                    if v_isSharedCheck_912_ == 0 {
                        v___x_907_ = v___x_887_;
                        v_isShared_908_ = v_isSharedCheck_912_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_905_);
                        crate::leanh::lean_dec(v___x_887_);
                        v___x_907_ = crate::leanh::lean_box(0);
                        v_isShared_908_ = v_isSharedCheck_912_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_870_) == 0 {
                    v_a_871_ = crate::leanh::lean_ctor_get(v___y_870_, 0);
                    v_isSharedCheck_878_ = (!crate::leanh::lean_is_exclusive(v___y_870_)) as u8;
                    if v_isSharedCheck_878_ == 0 {
                        v___x_873_ = v___y_870_;
                        v_isShared_874_ = v_isSharedCheck_878_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_871_);
                        crate::leanh::lean_dec(v___y_870_);
                        v___x_873_ = crate::leanh::lean_box(0);
                        v_isShared_874_ = v_isSharedCheck_878_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_879_ = crate::leanh::lean_ctor_get(v___y_870_, 0);
                    v_isSharedCheck_886_ = (!crate::leanh::lean_is_exclusive(v___y_870_)) as u8;
                    if v_isSharedCheck_886_ == 0 {
                        v___x_881_ = v___y_870_;
                        v_isShared_882_ = v_isSharedCheck_886_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_879_);
                        crate::leanh::lean_dec(v___y_870_);
                        v___x_881_ = crate::leanh::lean_box(0);
                        v_isShared_882_ = v_isSharedCheck_886_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_874_ == 0 {
                    v___x_876_ = v___x_873_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
                    v___x_876_ = v_reuseFailAlloc_877_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_876_;
            }
            4 => {
                if v_isShared_882_ == 0 {
                    v___x_884_ = v___x_881_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
                    v___x_884_ = v_reuseFailAlloc_885_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_884_;
            }
            6 => {
                if v___y_892_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_889_, 1);
                    v___x_893_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_888_, v_a_865_, v_a_867_);
                    crate::leanh::lean_dec(v_a_888_);
                    if crate::leanh::lean_obj_tag(v___x_893_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_893_, 1);
                        v___x_894_ = l_Lean_Elab_Term_getPatternVars(
                            v_pattern_861_,
                            v_a_862_,
                            v_a_863_,
                            v_a_864_,
                            v_a_865_,
                            v_a_866_,
                            v_a_867_,
                        );
                        v___y_870_ = v___x_894_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_pattern_861_);
                        v_a_895_ = crate::leanh::lean_ctor_get(v___x_893_, 0);
                        v_isSharedCheck_902_ = (!crate::leanh::lean_is_exclusive(v___x_893_)) as u8;
                        if v_isSharedCheck_902_ == 0 {
                            v___x_897_ = v___x_893_;
                            v_isShared_898_ = v_isSharedCheck_902_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_895_);
                            crate::leanh::lean_dec(v___x_893_);
                            v___x_897_ = crate::leanh::lean_box(0);
                            v_isShared_898_ = v_isSharedCheck_902_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_888_);
                    crate::leanh::lean_dec(v_pattern_861_);
                    v___y_870_ = v___x_889_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                if v_isShared_898_ == 0 {
                    v___x_900_ = v___x_897_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_901_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
                    v___x_900_ = v_reuseFailAlloc_901_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_900_;
            }
            9 => {
                if v_isShared_908_ == 0 {
                    v___x_910_ = v___x_907_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
                    v___x_910_ = v_reuseFailAlloc_911_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_getPatternVarsEx___boxed(
    mut v_pattern_913_: *mut crate::leanh::LeanObject,
    mut v_a_914_: *mut crate::leanh::LeanObject,
    mut v_a_915_: *mut crate::leanh::LeanObject,
    mut v_a_916_: *mut crate::leanh::LeanObject,
    mut v_a_917_: *mut crate::leanh::LeanObject,
    mut v_a_918_: *mut crate::leanh::LeanObject,
    mut v_a_919_: *mut crate::leanh::LeanObject,
    mut v_a_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_921_ = l_Lean_Elab_Do_getPatternVarsEx(
        v_pattern_913_,
        v_a_914_,
        v_a_915_,
        v_a_916_,
        v_a_917_,
        v_a_918_,
        v_a_919_,
    );
    crate::leanh::lean_dec(v_a_919_);
    crate::leanh::lean_dec_ref(v_a_918_);
    crate::leanh::lean_dec(v_a_917_);
    crate::leanh::lean_dec_ref(v_a_916_);
    crate::leanh::lean_dec(v_a_915_);
    crate::leanh::lean_dec_ref(v_a_914_);
    return v_res_921_;
}
pub unsafe fn l_Lean_Elab_Do_getPatternsVarsEx(
    mut v_patterns_922_: *mut crate::leanh::LeanObject,
    mut v_a_923_: *mut crate::leanh::LeanObject,
    mut v_a_924_: *mut crate::leanh::LeanObject,
    mut v_a_925_: *mut crate::leanh::LeanObject,
    mut v_a_926_: *mut crate::leanh::LeanObject,
    mut v_a_927_: *mut crate::leanh::LeanObject,
    mut v_a_928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_935_: u8 = 0;
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_939_: u8 = 0;
    let mut v_a_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_943_: u8 = 0;
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_947_: u8 = 0;
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_953_: u8 = 0;
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_959_: u8 = 0;
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_963_: u8 = 0;
    let mut v___x_964_: u8 = 0;
    let mut v___x_965_: u8 = 0;
    let mut v_a_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_948_ = l_Lean_Meta_saveState___redArg(v_a_926_, v_a_928_);
                if crate::leanh::lean_obj_tag(v___x_948_) == 0 {
                    v_a_949_ = crate::leanh::lean_ctor_get(v___x_948_, 0);
                    crate::leanh::lean_inc(v_a_949_);
                    crate::leanh::lean_dec_ref_known(v___x_948_, 1);
                    v___x_950_ = l_Lean_Elab_Term_Quotation_getPatternsVars(
                        v_patterns_922_,
                        v_a_923_,
                        v_a_924_,
                        v_a_925_,
                        v_a_926_,
                        v_a_927_,
                        v_a_928_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_950_) == 0 {
                        crate::leanh::lean_dec(v_a_949_);
                        v___y_931_ = v___x_950_;
                        state = 1;
                        continue;
                    } else {
                        v_a_951_ = crate::leanh::lean_ctor_get(v___x_950_, 0);
                        crate::leanh::lean_inc(v_a_951_);
                        v___x_964_ = l_Lean_Exception_isInterrupt(v_a_951_);
                        if v___x_964_ == 0 {
                            v___x_965_ = l_Lean_Exception_isRuntime(v_a_951_);
                            v___y_953_ = v___x_965_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_951_);
                            v___y_953_ = v___x_964_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_966_ = crate::leanh::lean_ctor_get(v___x_948_, 0);
                    v_isSharedCheck_973_ = (!crate::leanh::lean_is_exclusive(v___x_948_)) as u8;
                    if v_isSharedCheck_973_ == 0 {
                        v___x_968_ = v___x_948_;
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_966_);
                        crate::leanh::lean_dec(v___x_948_);
                        v___x_968_ = crate::leanh::lean_box(0);
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_931_) == 0 {
                    v_a_932_ = crate::leanh::lean_ctor_get(v___y_931_, 0);
                    v_isSharedCheck_939_ = (!crate::leanh::lean_is_exclusive(v___y_931_)) as u8;
                    if v_isSharedCheck_939_ == 0 {
                        v___x_934_ = v___y_931_;
                        v_isShared_935_ = v_isSharedCheck_939_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_932_);
                        crate::leanh::lean_dec(v___y_931_);
                        v___x_934_ = crate::leanh::lean_box(0);
                        v_isShared_935_ = v_isSharedCheck_939_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_940_ = crate::leanh::lean_ctor_get(v___y_931_, 0);
                    v_isSharedCheck_947_ = (!crate::leanh::lean_is_exclusive(v___y_931_)) as u8;
                    if v_isSharedCheck_947_ == 0 {
                        v___x_942_ = v___y_931_;
                        v_isShared_943_ = v_isSharedCheck_947_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_940_);
                        crate::leanh::lean_dec(v___y_931_);
                        v___x_942_ = crate::leanh::lean_box(0);
                        v_isShared_943_ = v_isSharedCheck_947_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_935_ == 0 {
                    v___x_937_ = v___x_934_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_938_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
                    v___x_937_ = v_reuseFailAlloc_938_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_937_;
            }
            4 => {
                if v_isShared_943_ == 0 {
                    v___x_945_ = v___x_942_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
                    v___x_945_ = v_reuseFailAlloc_946_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_945_;
            }
            6 => {
                if v___y_953_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_950_, 1);
                    v___x_954_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_949_, v_a_926_, v_a_928_);
                    crate::leanh::lean_dec(v_a_949_);
                    if crate::leanh::lean_obj_tag(v___x_954_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_954_, 1);
                        v___x_955_ = l_Lean_Elab_Term_getPatternsVars(
                            v_patterns_922_,
                            v_a_923_,
                            v_a_924_,
                            v_a_925_,
                            v_a_926_,
                            v_a_927_,
                            v_a_928_,
                        );
                        v___y_931_ = v___x_955_;
                        state = 1;
                        continue;
                    } else {
                        v_a_956_ = crate::leanh::lean_ctor_get(v___x_954_, 0);
                        v_isSharedCheck_963_ = (!crate::leanh::lean_is_exclusive(v___x_954_)) as u8;
                        if v_isSharedCheck_963_ == 0 {
                            v___x_958_ = v___x_954_;
                            v_isShared_959_ = v_isSharedCheck_963_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_956_);
                            crate::leanh::lean_dec(v___x_954_);
                            v___x_958_ = crate::leanh::lean_box(0);
                            v_isShared_959_ = v_isSharedCheck_963_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_949_);
                    v___y_931_ = v___x_950_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                if v_isShared_959_ == 0 {
                    v___x_961_ = v___x_958_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_962_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
                    v___x_961_ = v_reuseFailAlloc_962_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_961_;
            }
            9 => {
                if v_isShared_969_ == 0 {
                    v___x_971_ = v___x_968_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
                    v___x_971_ = v_reuseFailAlloc_972_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_getPatternsVarsEx___boxed(
    mut v_patterns_974_: *mut crate::leanh::LeanObject,
    mut v_a_975_: *mut crate::leanh::LeanObject,
    mut v_a_976_: *mut crate::leanh::LeanObject,
    mut v_a_977_: *mut crate::leanh::LeanObject,
    mut v_a_978_: *mut crate::leanh::LeanObject,
    mut v_a_979_: *mut crate::leanh::LeanObject,
    mut v_a_980_: *mut crate::leanh::LeanObject,
    mut v_a_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Lean_Elab_Do_getPatternsVarsEx(
        v_patterns_974_,
        v_a_975_,
        v_a_976_,
        v_a_977_,
        v_a_978_,
        v_a_979_,
        v_a_980_,
    );
    crate::leanh::lean_dec(v_a_980_);
    crate::leanh::lean_dec_ref(v_a_979_);
    crate::leanh::lean_dec(v_a_978_);
    crate::leanh::lean_dec_ref(v_a_977_);
    crate::leanh::lean_dec(v_a_976_);
    crate::leanh::lean_dec_ref(v_a_975_);
    crate::leanh::lean_dec_ref(v_patterns_974_);
    return v_res_982_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = crate::leanh::lean_box(1);
    v___x_984_ = l_Lean_MessageData_ofFormat(v___x_983_);
    return v___x_984_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__2;
    v___x_989_ = l_Lean_MessageData_ofFormat(v___x_988_);
    return v___x_989_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3(
    mut v_x_990_: *mut crate::leanh::LeanObject,
    mut v_x_991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_996_: u8 = 0;
    let mut v_before_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1000_: u8 = 0;
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1013_: u8 = 0;
    let mut v_unused_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1015_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_991_) == 0 {
                    return v_x_990_;
                } else {
                    v_head_992_ = crate::leanh::lean_ctor_get(v_x_991_, 0);
                    v_tail_993_ = crate::leanh::lean_ctor_get(v_x_991_, 1);
                    v_isSharedCheck_1015_ = (!crate::leanh::lean_is_exclusive(v_x_991_)) as u8;
                    if v_isSharedCheck_1015_ == 0 {
                        v___x_995_ = v_x_991_;
                        v_isShared_996_ = v_isSharedCheck_1015_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_993_);
                        crate::leanh::lean_inc(v_head_992_);
                        crate::leanh::lean_dec(v_x_991_);
                        v___x_995_ = crate::leanh::lean_box(0);
                        v_isShared_996_ = v_isSharedCheck_1015_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_997_ = crate::leanh::lean_ctor_get(v_head_992_, 0);
                v_isSharedCheck_1013_ = (!crate::leanh::lean_is_exclusive(v_head_992_)) as u8;
                if v_isSharedCheck_1013_ == 0 {
                    v_unused_1014_ = crate::leanh::lean_ctor_get(v_head_992_, 1);
                    crate::leanh::lean_dec(v_unused_1014_);
                    v___x_999_ = v_head_992_;
                    v_isShared_1000_ = v_isSharedCheck_1013_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_997_);
                    crate::leanh::lean_dec(v_head_992_);
                    v___x_999_ = crate::leanh::lean_box(0);
                    v_isShared_1000_ = v_isSharedCheck_1013_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1001_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_1000_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_999_, 7);
                    crate::leanh::lean_ctor_set(v___x_999_, 1, v___x_1001_);
                    crate::leanh::lean_ctor_set(v___x_999_, 0, v_x_990_);
                    v___x_1003_ = v___x_999_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1012_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_x_990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_1001_);
                    v___x_1003_ = v_reuseFailAlloc_1012_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1004_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3);
                if v_isShared_996_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_995_, 7);
                    crate::leanh::lean_ctor_set(v___x_995_, 1, v___x_1004_);
                    crate::leanh::lean_ctor_set(v___x_995_, 0, v___x_1003_);
                    v___x_1006_ = v___x_995_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1011_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___x_1004_);
                    v___x_1006_ = v_reuseFailAlloc_1011_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1007_ = l_Lean_MessageData_ofSyntax(v_before_997_);
                v___x_1008_ = l_Lean_indentD(v___x_1007_);
                v___x_1009_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1009_, 0, v___x_1006_);
                crate::leanh::lean_ctor_set(v___x_1009_, 1, v___x_1008_);
                v_x_990_ = v___x_1009_;
                v_x_991_ = v_tail_993_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2(
    mut v_opts_1016_: *mut crate::leanh::LeanObject,
    mut v_opt_1017_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1018_ = crate::leanh::lean_ctor_get(v_opt_1017_, 0);
    v_defValue_1019_ = crate::leanh::lean_ctor_get(v_opt_1017_, 1);
    v_map_1020_ = crate::leanh::lean_ctor_get(v_opts_1016_, 0);
    v___x_1021_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1020_,
            v_name_1018_,
        );
    if crate::leanh::lean_obj_tag(v___x_1021_) == 0 {
        let mut v___x_1022_: u8 = 0;
        v___x_1022_ = (crate::leanh::lean_unbox(v_defValue_1019_) as u8);
        return v___x_1022_;
    } else {
        let mut v_val_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1023_ = crate::leanh::lean_ctor_get(v___x_1021_, 0);
        crate::leanh::lean_inc(v_val_1023_);
        crate::leanh::lean_dec_ref_known(v___x_1021_, 1);
        if crate::leanh::lean_obj_tag(v_val_1023_) == 1 {
            let mut v_v_1024_: u8 = 0;
            v_v_1024_ = crate::leanh::lean_ctor_get_uint8(v_val_1023_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1023_, 0);
            return v_v_1024_;
        } else {
            let mut v___x_1025_: u8 = 0;
            crate::leanh::lean_dec(v_val_1023_);
            v___x_1025_ = (crate::leanh::lean_unbox(v_defValue_1019_) as u8);
            return v___x_1025_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2___boxed(
    mut v_opts_1026_: *mut crate::leanh::LeanObject,
    mut v_opt_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1028_: u8 = 0;
    let mut v_r_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2(v_opts_1026_, v_opt_1027_);
    crate::leanh::lean_dec_ref(v_opt_1027_);
    crate::leanh::lean_dec_ref(v_opts_1026_);
    v_r_1029_ = crate::leanh::lean_box((v_res_1028_) as usize);
    return v_r_1029_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__1;
    v___x_1034_ = l_Lean_MessageData_ofFormat(v___x_1033_);
    return v___x_1034_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(
    mut v_msgData_1035_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1036_: *mut crate::leanh::LeanObject,
    mut v___y_1037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: u8 = 0;
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1048_: u8 = 0;
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_unused_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1039_ = crate::leanh::lean_ctor_get(v___y_1037_, 2);
                v___x_1040_ = l_Lean_Elab_pp_macroStack;
                v___x_1041_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2(v_options_1039_, v___x_1040_);
                if v___x_1041_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_1036_);
                    v___x_1042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1042_, 0, v_msgData_1035_);
                    return v___x_1042_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_1036_) == 0 {
                        v___x_1043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1043_, 0, v_msgData_1035_);
                        return v___x_1043_;
                    } else {
                        v_head_1044_ = crate::leanh::lean_ctor_get(v_macroStack_1036_, 0);
                        crate::leanh::lean_inc(v_head_1044_);
                        v_after_1045_ = crate::leanh::lean_ctor_get(v_head_1044_, 1);
                        v_isSharedCheck_1060_ =
                            (!crate::leanh::lean_is_exclusive(v_head_1044_)) as u8;
                        if v_isSharedCheck_1060_ == 0 {
                            v_unused_1061_ = crate::leanh::lean_ctor_get(v_head_1044_, 0);
                            crate::leanh::lean_dec(v_unused_1061_);
                            v___x_1047_ = v_head_1044_;
                            v_isShared_1048_ = v_isSharedCheck_1060_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_1045_);
                            crate::leanh::lean_dec(v_head_1044_);
                            v___x_1047_ = crate::leanh::lean_box(0);
                            v_isShared_1048_ = v_isSharedCheck_1060_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1049_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_1048_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1047_, 7);
                    crate::leanh::lean_ctor_set(v___x_1047_, 1, v___x_1049_);
                    crate::leanh::lean_ctor_set(v___x_1047_, 0, v_msgData_1035_);
                    v___x_1051_ = v___x_1047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_msgData_1035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1049_);
                    v___x_1051_ = v_reuseFailAlloc_1059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1052_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2);
                v___x_1053_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1053_, 0, v___x_1051_);
                crate::leanh::lean_ctor_set(v___x_1053_, 1, v___x_1052_);
                v___x_1054_ = l_Lean_MessageData_ofSyntax(v_after_1045_);
                v___x_1055_ = l_Lean_indentD(v___x_1054_);
                v_msgData_1056_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_1056_, 0, v___x_1053_);
                crate::leanh::lean_ctor_set(v_msgData_1056_, 1, v___x_1055_);
                v___x_1057_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3(v_msgData_1056_, v_macroStack_1036_);
                v___x_1058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1058_, 0, v___x_1057_);
                return v___x_1058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___boxed(
    mut v_msgData_1062_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
    mut v___y_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(v_msgData_1062_, v_macroStack_1063_, v___y_1064_);
    crate::leanh::lean_dec_ref(v___y_1064_);
    return v_res_1066_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0(
    mut v_msgData_1067_: *mut crate::leanh::LeanObject,
    mut v___y_1068_: *mut crate::leanh::LeanObject,
    mut v___y_1069_: *mut crate::leanh::LeanObject,
    mut v___y_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1073_ = lean_st_ref_get(v___y_1071_);
    v_env_1074_ = crate::leanh::lean_ctor_get(v___x_1073_, 0);
    crate::leanh::lean_inc_ref(v_env_1074_);
    crate::leanh::lean_dec(v___x_1073_);
    v___x_1075_ = lean_st_ref_get(v___y_1069_);
    v_mctx_1076_ = crate::leanh::lean_ctor_get(v___x_1075_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1076_);
    crate::leanh::lean_dec(v___x_1075_);
    v_lctx_1077_ = crate::leanh::lean_ctor_get(v___y_1068_, 2);
    v_options_1078_ = crate::leanh::lean_ctor_get(v___y_1070_, 2);
    crate::leanh::lean_inc_ref(v_options_1078_);
    crate::leanh::lean_inc_ref(v_lctx_1077_);
    v___x_1079_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1079_, 0, v_env_1074_);
    crate::leanh::lean_ctor_set(v___x_1079_, 1, v_mctx_1076_);
    crate::leanh::lean_ctor_set(v___x_1079_, 2, v_lctx_1077_);
    crate::leanh::lean_ctor_set(v___x_1079_, 3, v_options_1078_);
    v___x_1080_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1080_, 0, v___x_1079_);
    crate::leanh::lean_ctor_set(v___x_1080_, 1, v_msgData_1067_);
    v___x_1081_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1081_, 0, v___x_1080_);
    return v___x_1081_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0___boxed(
    mut v_msgData_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
    mut v___y_1085_: *mut crate::leanh::LeanObject,
    mut v___y_1086_: *mut crate::leanh::LeanObject,
    mut v___y_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1088_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0(v_msgData_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
    crate::leanh::lean_dec(v___y_1086_);
    crate::leanh::lean_dec_ref(v___y_1085_);
    crate::leanh::lean_dec(v___y_1084_);
    crate::leanh::lean_dec_ref(v___y_1083_);
    return v_res_1088_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(
    mut v_msg_1089_: *mut crate::leanh::LeanObject,
    mut v___y_1090_: *mut crate::leanh::LeanObject,
    mut v___y_1091_: *mut crate::leanh::LeanObject,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1106_: u8 = 0;
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1097_ = crate::leanh::lean_ctor_get(v___y_1094_, 5);
                v___x_1098_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0(v_msg_1089_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
                v_a_1099_ = crate::leanh::lean_ctor_get(v___x_1098_, 0);
                crate::leanh::lean_inc(v_a_1099_);
                crate::leanh::lean_dec_ref(v___x_1098_);
                v_macroStack_1100_ = crate::leanh::lean_ctor_get(v___y_1090_, 1);
                v___x_1101_ = l_Lean_Elab_getBetterRef(v_ref_1097_, v_macroStack_1100_);
                crate::leanh::lean_inc(v_macroStack_1100_);
                v___x_1102_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(v_a_1099_, v_macroStack_1100_, v___y_1094_);
                v_a_1103_ = crate::leanh::lean_ctor_get(v___x_1102_, 0);
                v_isSharedCheck_1111_ = (!crate::leanh::lean_is_exclusive(v___x_1102_)) as u8;
                if v_isSharedCheck_1111_ == 0 {
                    v___x_1105_ = v___x_1102_;
                    v_isShared_1106_ = v_isSharedCheck_1111_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1103_);
                    crate::leanh::lean_dec(v___x_1102_);
                    v___x_1105_ = crate::leanh::lean_box(0);
                    v_isShared_1106_ = v_isSharedCheck_1111_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1107_, 0, v___x_1101_);
                crate::leanh::lean_ctor_set(v___x_1107_, 1, v_a_1103_);
                if v_isShared_1106_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1105_, 1);
                    crate::leanh::lean_ctor_set(v___x_1105_, 0, v___x_1107_);
                    v___x_1109_ = v___x_1105_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
                    v___x_1109_ = v_reuseFailAlloc_1110_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg___boxed(
    mut v_msg_1112_: *mut crate::leanh::LeanObject,
    mut v___y_1113_: *mut crate::leanh::LeanObject,
    mut v___y_1114_: *mut crate::leanh::LeanObject,
    mut v___y_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
    mut v___y_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
    mut v___y_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v_msg_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
    crate::leanh::lean_dec(v___y_1118_);
    crate::leanh::lean_dec_ref(v___y_1117_);
    crate::leanh::lean_dec(v___y_1116_);
    crate::leanh::lean_dec_ref(v___y_1115_);
    crate::leanh::lean_dec(v___y_1114_);
    crate::leanh::lean_dec_ref(v___y_1113_);
    return v_res_1120_;
}
pub unsafe fn _init_l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__5;
    v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
    return v___x_1132_;
}
pub unsafe fn l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(
    mut v_letId_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
    mut v_a_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
    mut v_a_1154_: *mut crate::leanh::LeanObject,
    mut v_a_1155_: *mut crate::leanh::LeanObject,
    mut v_a_1156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: u8 = 0;
    v___x_1158_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4;
    crate::leanh::lean_inc(v_letId_1150_);
    v___x_1159_ = l_Lean_Syntax_isOfKind(v_letId_1150_, v___x_1158_);
    if v___x_1159_ == 0 {
        let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1160_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6
            ),
            core::ptr::addr_of_mut!(
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6_once
            ),
            _init_l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6,
        );
        v___x_1161_ = l_Lean_MessageData_ofSyntax(v_letId_1150_);
        v___x_1162_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1160_);
        crate::leanh::lean_ctor_set(v___x_1162_, 1, v___x_1161_);
        v___x_1163_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_1162_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
        return v___x_1163_;
    } else {
        let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_id_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1167_: u8 = 0;
        v___x_1164_ = crate::leanh::lean_unsigned_to_nat(0);
        v_id_1165_ = l_Lean_Syntax_getArg(v_letId_1150_, v___x_1164_);
        v___x_1166_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8;
        crate::leanh::lean_inc(v_id_1165_);
        v___x_1167_ = l_Lean_Syntax_isOfKind(v_id_1165_, v___x_1166_);
        if v___x_1167_ == 0 {
            let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1169_: u8 = 0;
            v___x_1168_ =
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10;
            crate::leanh::lean_inc(v_id_1165_);
            v___x_1169_ = l_Lean_Syntax_isOfKind(v_id_1165_, v___x_1168_);
            if v___x_1169_ == 0 {
                let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1171_: u8 = 0;
                v___x_1170_ =
                    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12;
                crate::leanh::lean_inc(v_id_1165_);
                v___x_1171_ = l_Lean_Syntax_isOfKind(v_id_1165_, v___x_1170_);
                if v___x_1171_ == 0 {
                    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_id_1165_);
                    v___x_1172_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6_once), _init_l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6);
                    v___x_1173_ = l_Lean_MessageData_ofSyntax(v_letId_1150_);
                    v___x_1174_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1174_, 0, v___x_1172_);
                    crate::leanh::lean_ctor_set(v___x_1174_, 1, v___x_1173_);
                    v___x_1175_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_1174_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
                    return v___x_1175_;
                } else {
                    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_letId_1150_);
                    v___x_1176_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__14;
                    v___x_1177_ = l_Lean_HygieneInfo_mkIdent(v_id_1165_, v___x_1176_, v___x_1171_);
                    crate::leanh::lean_dec(v_id_1165_);
                    v___x_1178_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1179_ = lean_mk_empty_array_with_capacity(v___x_1178_);
                    v___x_1180_ = lean_array_push(v___x_1179_, v___x_1177_);
                    v___x_1181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1181_, 0, v___x_1180_);
                    return v___x_1181_;
                }
            } else {
                let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_letId_1150_);
                v___x_1182_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1183_ = lean_mk_empty_array_with_capacity(v___x_1182_);
                v___x_1184_ = lean_array_push(v___x_1183_, v_id_1165_);
                v___x_1185_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1185_, 0, v___x_1184_);
                return v___x_1185_;
            }
        } else {
            let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_id_1165_);
            crate::leanh::lean_dec(v_letId_1150_);
            v___x_1186_ =
                l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15;
            v___x_1187_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1187_, 0, v___x_1186_);
            return v___x_1187_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___boxed(
    mut v_letId_1188_: *mut crate::leanh::LeanObject,
    mut v_a_1189_: *mut crate::leanh::LeanObject,
    mut v_a_1190_: *mut crate::leanh::LeanObject,
    mut v_a_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
    mut v_a_1193_: *mut crate::leanh::LeanObject,
    mut v_a_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1196_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(
        v_letId_1188_,
        v_a_1189_,
        v_a_1190_,
        v_a_1191_,
        v_a_1192_,
        v_a_1193_,
        v_a_1194_,
    );
    crate::leanh::lean_dec(v_a_1194_);
    crate::leanh::lean_dec_ref(v_a_1193_);
    crate::leanh::lean_dec(v_a_1192_);
    crate::leanh::lean_dec_ref(v_a_1191_);
    crate::leanh::lean_dec(v_a_1190_);
    crate::leanh::lean_dec_ref(v_a_1189_);
    return v_res_1196_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0(
    mut v_00_u03b1_1197_: *mut crate::leanh::LeanObject,
    mut v_msg_1198_: *mut crate::leanh::LeanObject,
    mut v___y_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
    mut v___y_1201_: *mut crate::leanh::LeanObject,
    mut v___y_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v_msg_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
    return v___x_1206_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___boxed(
    mut v_00_u03b1_1207_: *mut crate::leanh::LeanObject,
    mut v_msg_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1216_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0(v_00_u03b1_1207_, v_msg_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
    crate::leanh::lean_dec(v___y_1214_);
    crate::leanh::lean_dec_ref(v___y_1213_);
    crate::leanh::lean_dec(v___y_1212_);
    crate::leanh::lean_dec_ref(v___y_1211_);
    crate::leanh::lean_dec(v___y_1210_);
    crate::leanh::lean_dec_ref(v___y_1209_);
    return v_res_1216_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1(
    mut v_msgData_1217_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1218_: *mut crate::leanh::LeanObject,
    mut v___y_1219_: *mut crate::leanh::LeanObject,
    mut v___y_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
    mut v___y_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1226_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(v_msgData_1217_, v_macroStack_1218_, v___y_1223_);
    return v___x_1226_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___boxed(
    mut v_msgData_1227_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
    mut v___y_1232_: *mut crate::leanh::LeanObject,
    mut v___y_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1236_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1(v_msgData_1227_, v_macroStack_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
    crate::leanh::lean_dec(v___y_1234_);
    crate::leanh::lean_dec_ref(v___y_1233_);
    crate::leanh::lean_dec(v___y_1232_);
    crate::leanh::lean_dec_ref(v___y_1231_);
    crate::leanh::lean_dec(v___y_1230_);
    crate::leanh::lean_dec_ref(v___y_1229_);
    return v_res_1236_;
}
pub unsafe fn l_Lean_Elab_Do_getLetIdDeclVars(
    mut v_letIdDecl_1237_: *mut crate::leanh::LeanObject,
    mut v_a_1238_: *mut crate::leanh::LeanObject,
    mut v_a_1239_: *mut crate::leanh::LeanObject,
    mut v_a_1240_: *mut crate::leanh::LeanObject,
    mut v_a_1241_: *mut crate::leanh::LeanObject,
    mut v_a_1242_: *mut crate::leanh::LeanObject,
    mut v_a_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1245_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1246_ = l_Lean_Syntax_getArg(v_letIdDecl_1237_, v___x_1245_);
    v___x_1247_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(
        v___x_1246_,
        v_a_1238_,
        v_a_1239_,
        v_a_1240_,
        v_a_1241_,
        v_a_1242_,
        v_a_1243_,
    );
    return v___x_1247_;
}
pub unsafe fn l_Lean_Elab_Do_getLetIdDeclVars___boxed(
    mut v_letIdDecl_1248_: *mut crate::leanh::LeanObject,
    mut v_a_1249_: *mut crate::leanh::LeanObject,
    mut v_a_1250_: *mut crate::leanh::LeanObject,
    mut v_a_1251_: *mut crate::leanh::LeanObject,
    mut v_a_1252_: *mut crate::leanh::LeanObject,
    mut v_a_1253_: *mut crate::leanh::LeanObject,
    mut v_a_1254_: *mut crate::leanh::LeanObject,
    mut v_a_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1256_ = l_Lean_Elab_Do_getLetIdDeclVars(
        v_letIdDecl_1248_,
        v_a_1249_,
        v_a_1250_,
        v_a_1251_,
        v_a_1252_,
        v_a_1253_,
        v_a_1254_,
    );
    crate::leanh::lean_dec(v_a_1254_);
    crate::leanh::lean_dec_ref(v_a_1253_);
    crate::leanh::lean_dec(v_a_1252_);
    crate::leanh::lean_dec_ref(v_a_1251_);
    crate::leanh::lean_dec(v_a_1250_);
    crate::leanh::lean_dec_ref(v_a_1249_);
    crate::leanh::lean_dec(v_letIdDecl_1248_);
    return v_res_1256_;
}
pub unsafe fn l_Lean_Elab_Do_getLetPatDeclVars(
    mut v_letPatDecl_1257_: *mut crate::leanh::LeanObject,
    mut v_a_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
    mut v_a_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
    mut v_a_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1265_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1266_ = l_Lean_Syntax_getArg(v_letPatDecl_1257_, v___x_1265_);
    v___x_1267_ = l_Lean_Elab_Do_getPatternVarsEx(
        v___x_1266_,
        v_a_1258_,
        v_a_1259_,
        v_a_1260_,
        v_a_1261_,
        v_a_1262_,
        v_a_1263_,
    );
    return v___x_1267_;
}
pub unsafe fn l_Lean_Elab_Do_getLetPatDeclVars___boxed(
    mut v_letPatDecl_1268_: *mut crate::leanh::LeanObject,
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_a_1270_: *mut crate::leanh::LeanObject,
    mut v_a_1271_: *mut crate::leanh::LeanObject,
    mut v_a_1272_: *mut crate::leanh::LeanObject,
    mut v_a_1273_: *mut crate::leanh::LeanObject,
    mut v_a_1274_: *mut crate::leanh::LeanObject,
    mut v_a_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Lean_Elab_Do_getLetPatDeclVars(
        v_letPatDecl_1268_,
        v_a_1269_,
        v_a_1270_,
        v_a_1271_,
        v_a_1272_,
        v_a_1273_,
        v_a_1274_,
    );
    crate::leanh::lean_dec(v_a_1274_);
    crate::leanh::lean_dec_ref(v_a_1273_);
    crate::leanh::lean_dec(v_a_1272_);
    crate::leanh::lean_dec_ref(v_a_1271_);
    crate::leanh::lean_dec(v_a_1270_);
    crate::leanh::lean_dec_ref(v_a_1269_);
    crate::leanh::lean_dec(v_letPatDecl_1268_);
    return v_res_1276_;
}
pub unsafe fn l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars(
    mut v_letEqnsDecl_1277_: *mut crate::leanh::LeanObject,
    mut v_a_1278_: *mut crate::leanh::LeanObject,
    mut v_a_1279_: *mut crate::leanh::LeanObject,
    mut v_a_1280_: *mut crate::leanh::LeanObject,
    mut v_a_1281_: *mut crate::leanh::LeanObject,
    mut v_a_1282_: *mut crate::leanh::LeanObject,
    mut v_a_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1286_ = l_Lean_Syntax_getArg(v_letEqnsDecl_1277_, v___x_1285_);
    v___x_1287_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(
        v___x_1286_,
        v_a_1278_,
        v_a_1279_,
        v_a_1280_,
        v_a_1281_,
        v_a_1282_,
        v_a_1283_,
    );
    return v___x_1287_;
}
pub unsafe fn l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars___boxed(
    mut v_letEqnsDecl_1288_: *mut crate::leanh::LeanObject,
    mut v_a_1289_: *mut crate::leanh::LeanObject,
    mut v_a_1290_: *mut crate::leanh::LeanObject,
    mut v_a_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_a_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars(
        v_letEqnsDecl_1288_,
        v_a_1289_,
        v_a_1290_,
        v_a_1291_,
        v_a_1292_,
        v_a_1293_,
        v_a_1294_,
    );
    crate::leanh::lean_dec(v_a_1294_);
    crate::leanh::lean_dec_ref(v_a_1293_);
    crate::leanh::lean_dec(v_a_1292_);
    crate::leanh::lean_dec_ref(v_a_1291_);
    crate::leanh::lean_dec(v_a_1290_);
    crate::leanh::lean_dec_ref(v_a_1289_);
    crate::leanh::lean_dec(v_letEqnsDecl_1288_);
    return v_res_1296_;
}
pub unsafe fn _init_l_Lean_Elab_Do_getLetDeclVars___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = l_Lean_Elab_Do_getLetDeclVars___closed__2;
    v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
    return v___x_1305_;
}
pub unsafe fn l_Lean_Elab_Do_getLetDeclVars(
    mut v_letDecl_1324_: *mut crate::leanh::LeanObject,
    mut v_a_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
    mut v_a_1327_: *mut crate::leanh::LeanObject,
    mut v_a_1328_: *mut crate::leanh::LeanObject,
    mut v_a_1329_: *mut crate::leanh::LeanObject,
    mut v_a_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    v___x_1332_ = l_Lean_Elab_Do_getLetDeclVars___closed__1;
    crate::leanh::lean_inc(v_letDecl_1324_);
    v___x_1333_ = l_Lean_Syntax_isOfKind(v_letDecl_1324_, v___x_1332_);
    if v___x_1333_ == 0 {
        let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1334_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Do_getLetDeclVars___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Elab_Do_getLetDeclVars___closed__3_once),
            _init_l_Lean_Elab_Do_getLetDeclVars___closed__3,
        );
        v___x_1335_ = crate::leanh::lean_box(0);
        v___x_1336_ = l_Lean_Syntax_formatStx(v_letDecl_1324_, v___x_1335_, v___x_1333_);
        v___x_1337_ = l_Std_Format_defWidth;
        v___x_1338_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1339_ = l_Std_Format_pretty(v___x_1336_, v___x_1337_, v___x_1338_, v___x_1338_);
        v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
        v___x_1341_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1341_, 0, v___x_1334_);
        crate::leanh::lean_ctor_set(v___x_1341_, 1, v___x_1340_);
        v___x_1342_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_1341_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
        return v___x_1342_;
    } else {
        let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_letIdDecl_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1346_: u8 = 0;
        v___x_1343_ = crate::leanh::lean_unsigned_to_nat(0);
        v_letIdDecl_1344_ = l_Lean_Syntax_getArg(v_letDecl_1324_, v___x_1343_);
        v___x_1345_ = l_Lean_Elab_Do_getLetDeclVars___closed__5;
        crate::leanh::lean_inc(v_letIdDecl_1344_);
        v___x_1346_ = l_Lean_Syntax_isOfKind(v_letIdDecl_1344_, v___x_1345_);
        if v___x_1346_ == 0 {
            let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1348_: u8 = 0;
            v___x_1347_ = l_Lean_Elab_Do_getLetDeclVars___closed__7;
            crate::leanh::lean_inc(v_letIdDecl_1344_);
            v___x_1348_ = l_Lean_Syntax_isOfKind(v_letIdDecl_1344_, v___x_1347_);
            if v___x_1348_ == 0 {
                if v___x_1348_ == 0 {
                    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1350_: u8 = 0;
                    v___x_1349_ = l_Lean_Elab_Do_getLetDeclVars___closed__9;
                    crate::leanh::lean_inc(v_letIdDecl_1344_);
                    v___x_1350_ = l_Lean_Syntax_isOfKind(v_letIdDecl_1344_, v___x_1349_);
                    if v___x_1350_ == 0 {
                        let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_letIdDecl_1344_);
                        v___x_1351_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Do_getLetDeclVars___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_Elab_Do_getLetDeclVars___closed__3_once),
                            _init_l_Lean_Elab_Do_getLetDeclVars___closed__3,
                        );
                        v___x_1352_ = crate::leanh::lean_box(0);
                        v___x_1353_ =
                            l_Lean_Syntax_formatStx(v_letDecl_1324_, v___x_1352_, v___x_1350_);
                        v___x_1354_ = l_Std_Format_defWidth;
                        v___x_1355_ =
                            l_Std_Format_pretty(v___x_1353_, v___x_1354_, v___x_1343_, v___x_1343_);
                        v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
                        v___x_1357_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1351_);
                        crate::leanh::lean_ctor_set(v___x_1357_, 1, v___x_1356_);
                        v___x_1358_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_1357_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
                        return v___x_1358_;
                    } else {
                        let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_letDecl_1324_);
                        v___x_1359_ =
                            l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars(
                                v_letIdDecl_1344_,
                                v_a_1325_,
                                v_a_1326_,
                                v_a_1327_,
                                v_a_1328_,
                                v_a_1329_,
                                v_a_1330_,
                            );
                        crate::leanh::lean_dec(v_letIdDecl_1344_);
                        return v___x_1359_;
                    }
                } else {
                    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_letDecl_1324_);
                    v___x_1360_ = l_Lean_Elab_Do_getLetPatDeclVars(
                        v_letIdDecl_1344_,
                        v_a_1325_,
                        v_a_1326_,
                        v_a_1327_,
                        v_a_1328_,
                        v_a_1329_,
                        v_a_1330_,
                    );
                    crate::leanh::lean_dec(v_letIdDecl_1344_);
                    return v___x_1360_;
                }
            } else {
                let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_letDecl_1324_);
                v___x_1361_ = l_Lean_Elab_Do_getLetPatDeclVars(
                    v_letIdDecl_1344_,
                    v_a_1325_,
                    v_a_1326_,
                    v_a_1327_,
                    v_a_1328_,
                    v_a_1329_,
                    v_a_1330_,
                );
                crate::leanh::lean_dec(v_letIdDecl_1344_);
                return v___x_1361_;
            }
        } else {
            let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_letDecl_1324_);
            v___x_1362_ = l_Lean_Elab_Do_getLetIdDeclVars(
                v_letIdDecl_1344_,
                v_a_1325_,
                v_a_1326_,
                v_a_1327_,
                v_a_1328_,
                v_a_1329_,
                v_a_1330_,
            );
            crate::leanh::lean_dec(v_letIdDecl_1344_);
            return v___x_1362_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_getLetDeclVars___boxed(
    mut v_letDecl_1363_: *mut crate::leanh::LeanObject,
    mut v_a_1364_: *mut crate::leanh::LeanObject,
    mut v_a_1365_: *mut crate::leanh::LeanObject,
    mut v_a_1366_: *mut crate::leanh::LeanObject,
    mut v_a_1367_: *mut crate::leanh::LeanObject,
    mut v_a_1368_: *mut crate::leanh::LeanObject,
    mut v_a_1369_: *mut crate::leanh::LeanObject,
    mut v_a_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1371_ = l_Lean_Elab_Do_getLetDeclVars(
        v_letDecl_1363_,
        v_a_1364_,
        v_a_1365_,
        v_a_1366_,
        v_a_1367_,
        v_a_1368_,
        v_a_1369_,
    );
    crate::leanh::lean_dec(v_a_1369_);
    crate::leanh::lean_dec_ref(v_a_1368_);
    crate::leanh::lean_dec(v_a_1367_);
    crate::leanh::lean_dec_ref(v_a_1366_);
    crate::leanh::lean_dec(v_a_1365_);
    crate::leanh::lean_dec_ref(v_a_1364_);
    return v_res_1371_;
}
pub unsafe fn l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars(
    mut v_letRecDecl_1372_: *mut crate::leanh::LeanObject,
    mut v_a_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
    mut v_a_1375_: *mut crate::leanh::LeanObject,
    mut v_a_1376_: *mut crate::leanh::LeanObject,
    mut v_a_1377_: *mut crate::leanh::LeanObject,
    mut v_a_1378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1381_ = l_Lean_Syntax_getArg(v_letRecDecl_1372_, v___x_1380_);
    v___x_1382_ = l_Lean_Elab_Do_getLetDeclVars(
        v___x_1381_,
        v_a_1373_,
        v_a_1374_,
        v_a_1375_,
        v_a_1376_,
        v_a_1377_,
        v_a_1378_,
    );
    return v___x_1382_;
}
pub unsafe fn l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars___boxed(
    mut v_letRecDecl_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_a_1387_: *mut crate::leanh::LeanObject,
    mut v_a_1388_: *mut crate::leanh::LeanObject,
    mut v_a_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1391_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars(
        v_letRecDecl_1383_,
        v_a_1384_,
        v_a_1385_,
        v_a_1386_,
        v_a_1387_,
        v_a_1388_,
        v_a_1389_,
    );
    crate::leanh::lean_dec(v_a_1389_);
    crate::leanh::lean_dec_ref(v_a_1388_);
    crate::leanh::lean_dec(v_a_1387_);
    crate::leanh::lean_dec_ref(v_a_1386_);
    crate::leanh::lean_dec(v_a_1385_);
    crate::leanh::lean_dec_ref(v_a_1384_);
    crate::leanh::lean_dec(v_letRecDecl_1383_);
    return v_res_1391_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = crate::leanh::lean_box(0);
    v___x_1393_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1394_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1394_, 0, v___x_1393_);
    crate::leanh::lean_ctor_set(v___x_1394_, 1, v___x_1392_);
    return v___x_1394_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg___closed__0);
    v___x_1397_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1397_, 0, v___x_1396_);
    return v___x_1397_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg___boxed(
    mut v___y_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1399_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg();
    return v_res_1399_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0(
    mut v_00_u03b1_1400_: *mut crate::leanh::LeanObject,
    mut v___y_1401_: *mut crate::leanh::LeanObject,
    mut v___y_1402_: *mut crate::leanh::LeanObject,
    mut v___y_1403_: *mut crate::leanh::LeanObject,
    mut v___y_1404_: *mut crate::leanh::LeanObject,
    mut v___y_1405_: *mut crate::leanh::LeanObject,
    mut v___y_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg();
    return v___x_1408_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___boxed(
    mut v_00_u03b1_1409_: *mut crate::leanh::LeanObject,
    mut v___y_1410_: *mut crate::leanh::LeanObject,
    mut v___y_1411_: *mut crate::leanh::LeanObject,
    mut v___y_1412_: *mut crate::leanh::LeanObject,
    mut v___y_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1417_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0(
            v_00_u03b1_1409_,
            v___y_1410_,
            v___y_1411_,
            v___y_1412_,
            v___y_1413_,
            v___y_1414_,
            v___y_1415_,
        );
    crate::leanh::lean_dec(v___y_1415_);
    crate::leanh::lean_dec_ref(v___y_1414_);
    crate::leanh::lean_dec(v___y_1413_);
    crate::leanh::lean_dec_ref(v___y_1412_);
    crate::leanh::lean_dec(v___y_1411_);
    crate::leanh::lean_dec_ref(v___y_1410_);
    return v_res_1417_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2(
    mut v_as_1418_: *mut crate::leanh::LeanObject,
    mut v_sz_1419_: usize,
    mut v_i_1420_: usize,
    mut v_b_1421_: *mut crate::leanh::LeanObject,
    mut v___y_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: usize = 0;
    let mut v___x_1436_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1429_ = lean_usize_dec_lt(v_i_1420_, v_sz_1419_);
                if v___x_1429_ == 0 {
                    v___x_1430_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1430_, 0, v_b_1421_);
                    return v___x_1430_;
                } else {
                    v_a_1431_ = lean_array_uget_borrowed(v_as_1418_, v_i_1420_);
                    v___x_1432_ =
                        l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars(
                            v_a_1431_,
                            v___y_1422_,
                            v___y_1423_,
                            v___y_1424_,
                            v___y_1425_,
                            v___y_1426_,
                            v___y_1427_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1432_) == 0 {
                        v_a_1433_ = crate::leanh::lean_ctor_get(v___x_1432_, 0);
                        crate::leanh::lean_inc(v_a_1433_);
                        crate::leanh::lean_dec_ref_known(v___x_1432_, 1);
                        v___x_1434_ = l_Array_append___redArg(v_b_1421_, v_a_1433_);
                        crate::leanh::lean_dec(v_a_1433_);
                        v___x_1435_ = 1usize;
                        v___x_1436_ = lean_usize_add(v_i_1420_, v___x_1435_);
                        v_i_1420_ = v___x_1436_;
                        v_b_1421_ = v___x_1434_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1421_);
                        return v___x_1432_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2___boxed(
    mut v_as_1438_: *mut crate::leanh::LeanObject,
    mut v_sz_1439_: *mut crate::leanh::LeanObject,
    mut v_i_1440_: *mut crate::leanh::LeanObject,
    mut v_b_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1449_: usize = 0;
    let mut v_i_boxed_1450_: usize = 0;
    let mut v_res_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1449_ = crate::leanh::lean_unbox_usize(v_sz_1439_);
    crate::leanh::lean_dec(v_sz_1439_);
    v_i_boxed_1450_ = crate::leanh::lean_unbox_usize(v_i_1440_);
    crate::leanh::lean_dec(v_i_1440_);
    v_res_1451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2(v_as_1438_, v_sz_boxed_1449_, v_i_boxed_1450_, v_b_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
    crate::leanh::lean_dec(v___y_1447_);
    crate::leanh::lean_dec_ref(v___y_1446_);
    crate::leanh::lean_dec(v___y_1445_);
    crate::leanh::lean_dec_ref(v___y_1444_);
    crate::leanh::lean_dec(v___y_1443_);
    crate::leanh::lean_dec_ref(v___y_1442_);
    crate::leanh::lean_dec_ref(v_as_1438_);
    return v_res_1451_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(
    mut v___x_1452_: u8,
    mut v_as_1453_: *mut crate::leanh::LeanObject,
    mut v_i_1454_: usize,
    mut v_stop_1455_: usize,
    mut v_b_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: usize = 0;
    let mut v___x_1460_: usize = 0;
    let mut v___x_1462_: u8 = 0;
    let mut v_fst_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v_snd_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1473_: u8 = 0;
    let mut v_unused_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1485_: u8 = 0;
    let mut v_unused_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1462_ = lean_usize_dec_eq(v_i_1454_, v_stop_1455_);
                if v___x_1462_ == 0 {
                    v_fst_1463_ = crate::leanh::lean_ctor_get(v_b_1456_, 0);
                    v___x_1464_ = (crate::leanh::lean_unbox(v_fst_1463_) as u8);
                    if v___x_1464_ == 0 {
                        v_snd_1465_ = crate::leanh::lean_ctor_get(v_b_1456_, 1);
                        v_isSharedCheck_1473_ = (!crate::leanh::lean_is_exclusive(v_b_1456_)) as u8;
                        if v_isSharedCheck_1473_ == 0 {
                            v_unused_1474_ = crate::leanh::lean_ctor_get(v_b_1456_, 0);
                            crate::leanh::lean_dec(v_unused_1474_);
                            v___x_1467_ = v_b_1456_;
                            v_isShared_1468_ = v_isSharedCheck_1473_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1465_);
                            crate::leanh::lean_dec(v_b_1456_);
                            v___x_1467_ = crate::leanh::lean_box(0);
                            v_isShared_1468_ = v_isSharedCheck_1473_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_1475_ = crate::leanh::lean_ctor_get(v_b_1456_, 1);
                        v_isSharedCheck_1485_ = (!crate::leanh::lean_is_exclusive(v_b_1456_)) as u8;
                        if v_isSharedCheck_1485_ == 0 {
                            v_unused_1486_ = crate::leanh::lean_ctor_get(v_b_1456_, 0);
                            crate::leanh::lean_dec(v_unused_1486_);
                            v___x_1477_ = v_b_1456_;
                            v_isShared_1478_ = v_isSharedCheck_1485_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1475_);
                            crate::leanh::lean_dec(v_b_1456_);
                            v___x_1477_ = crate::leanh::lean_box(0);
                            v_isShared_1478_ = v_isSharedCheck_1485_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_1456_;
                }
            }
            1 => {
                v___x_1459_ = 1usize;
                v___x_1460_ = lean_usize_add(v_i_1454_, v___x_1459_);
                v_i_1454_ = v___x_1460_;
                v_b_1456_ = v___y_1458_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1469_ = crate::leanh::lean_box((v___x_1452_) as usize);
                if v_isShared_1468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1469_);
                    v___x_1471_ = v___x_1467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1472_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_snd_1465_);
                    v___x_1471_ = v_reuseFailAlloc_1472_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1458_ = v___x_1471_;
                state = 1;
                continue;
            }
            4 => {
                v___x_1479_ = lean_array_uget_borrowed(v_as_1453_, v_i_1454_);
                crate::leanh::lean_inc(v___x_1479_);
                v___x_1480_ = lean_array_push(v_snd_1475_, v___x_1479_);
                v___x_1481_ = crate::leanh::lean_box((v___x_1462_) as usize);
                if v_isShared_1478_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1477_, 1, v___x_1480_);
                    crate::leanh::lean_ctor_set(v___x_1477_, 0, v___x_1481_);
                    v___x_1483_ = v___x_1477_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1484_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___x_1480_);
                    v___x_1483_ = v_reuseFailAlloc_1484_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1458_ = v___x_1483_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3___boxed(
    mut v___x_1487_: *mut crate::leanh::LeanObject,
    mut v_as_1488_: *mut crate::leanh::LeanObject,
    mut v_i_1489_: *mut crate::leanh::LeanObject,
    mut v_stop_1490_: *mut crate::leanh::LeanObject,
    mut v_b_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1821__boxed_1492_: u8 = 0;
    let mut v_i_boxed_1493_: usize = 0;
    let mut v_stop_boxed_1494_: usize = 0;
    let mut v_res_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1821__boxed_1492_ = (crate::leanh::lean_unbox(v___x_1487_) as u8);
    v_i_boxed_1493_ = crate::leanh::lean_unbox_usize(v_i_1489_);
    crate::leanh::lean_dec(v_i_1489_);
    v_stop_boxed_1494_ = crate::leanh::lean_unbox_usize(v_stop_1490_);
    crate::leanh::lean_dec(v_stop_1490_);
    v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(v___x_1821__boxed_1492_, v_as_1488_, v_i_boxed_1493_, v_stop_boxed_1494_, v_b_1491_);
    crate::leanh::lean_dec_ref(v_as_1488_);
    return v_res_1495_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1(
    mut v_sz_1502_: usize,
    mut v_i_1503_: usize,
    mut v_bs_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1505_: u8 = 0;
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: u8 = 0;
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: usize = 0;
    let mut v___x_1514_: usize = 0;
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1505_ = lean_usize_dec_lt(v_i_1503_, v_sz_1502_);
                if v___x_1505_ == 0 {
                    v___x_1506_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1506_, 0, v_bs_1504_);
                    return v___x_1506_;
                } else {
                    v_v_1507_ = lean_array_uget(v_bs_1504_, v_i_1503_);
                    v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___closed__1;
                    crate::leanh::lean_inc(v_v_1507_);
                    v___x_1509_ = l_Lean_Syntax_isOfKind(v_v_1507_, v___x_1508_);
                    if v___x_1509_ == 0 {
                        crate::leanh::lean_dec(v_v_1507_);
                        crate::leanh::lean_dec_ref(v_bs_1504_);
                        v___x_1510_ = crate::leanh::lean_box(0);
                        return v___x_1510_;
                    } else {
                        v___x_1511_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1512_ = lean_array_uset(v_bs_1504_, v_i_1503_, v___x_1511_);
                        v___x_1513_ = 1usize;
                        v___x_1514_ = lean_usize_add(v_i_1503_, v___x_1513_);
                        v___x_1515_ = lean_array_uset(v_bs_x27_1512_, v_i_1503_, v_v_1507_);
                        v_i_1503_ = v___x_1514_;
                        v_bs_1504_ = v___x_1515_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___boxed(
    mut v_sz_1517_: *mut crate::leanh::LeanObject,
    mut v_i_1518_: *mut crate::leanh::LeanObject,
    mut v_bs_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1520_: usize = 0;
    let mut v_i_boxed_1521_: usize = 0;
    let mut v_res_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1520_ = crate::leanh::lean_unbox_usize(v_sz_1517_);
    crate::leanh::lean_dec(v_sz_1517_);
    v_i_boxed_1521_ = crate::leanh::lean_unbox_usize(v_i_1518_);
    crate::leanh::lean_dec(v_i_1518_);
    v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1(v_sz_boxed_1520_, v_i_boxed_1521_, v_bs_1519_);
    return v_res_1522_;
}
pub unsafe fn l_Lean_Elab_Do_getLetRecDeclsVars(
    mut v_letRecDecls_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
    mut v_a_1534_: *mut crate::leanh::LeanObject,
    mut v_a_1535_: *mut crate::leanh::LeanObject,
    mut v_a_1536_: *mut crate::leanh::LeanObject,
    mut v_a_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: u8 = 0;
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1545_: usize = 0;
    let mut v___x_1546_: usize = 0;
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allVars_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1551_: usize = 0;
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: u8 = 0;
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: u8 = 0;
    let mut v___x_1561_: usize = 0;
    let mut v___x_1562_: usize = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: usize = 0;
    let mut v___x_1566_: usize = 0;
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1539_ = l_Lean_Elab_Do_getLetRecDeclsVars___closed__1;
                crate::leanh::lean_inc(v_letRecDecls_1531_);
                v___x_1540_ = l_Lean_Syntax_isOfKind(v_letRecDecls_1531_, v___x_1539_);
                if v___x_1540_ == 0 {
                    crate::leanh::lean_dec(v_letRecDecls_1531_);
                    v___x_1541_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg();
                    return v___x_1541_;
                } else {
                    v___x_1542_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1553_ = l_Lean_Syntax_getArg(v_letRecDecls_1531_, v___x_1542_);
                    crate::leanh::lean_dec(v_letRecDecls_1531_);
                    v___x_1554_ = l_Lean_Syntax_getArgs(v___x_1553_);
                    crate::leanh::lean_dec(v___x_1553_);
                    v___x_1555_ = l_Lean_Elab_Do_getLetRecDeclsVars___closed__2;
                    v___x_1556_ = lean_array_get_size(v___x_1554_);
                    v___x_1557_ = lean_nat_dec_lt(v___x_1542_, v___x_1556_);
                    if v___x_1557_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1554_);
                        v___y_1544_ = v___x_1555_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1558_ = crate::leanh::lean_box((v___x_1540_) as usize);
                        v___x_1559_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1559_, 0, v___x_1558_);
                        crate::leanh::lean_ctor_set(v___x_1559_, 1, v___x_1555_);
                        v___x_1560_ = lean_nat_dec_le(v___x_1556_, v___x_1556_);
                        if v___x_1560_ == 0 {
                            if v___x_1557_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1559_, 2);
                                crate::leanh::lean_dec_ref(v___x_1554_);
                                v___y_1544_ = v___x_1555_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1561_ = 0usize;
                                v___x_1562_ = lean_usize_of_nat(v___x_1556_);
                                v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(v___x_1540_, v___x_1554_, v___x_1561_, v___x_1562_, v___x_1559_);
                                crate::leanh::lean_dec_ref(v___x_1554_);
                                v_snd_1564_ = crate::leanh::lean_ctor_get(v___x_1563_, 1);
                                crate::leanh::lean_inc(v_snd_1564_);
                                crate::leanh::lean_dec_ref(v___x_1563_);
                                v___y_1544_ = v_snd_1564_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1565_ = 0usize;
                            v___x_1566_ = lean_usize_of_nat(v___x_1556_);
                            v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(v___x_1540_, v___x_1554_, v___x_1565_, v___x_1566_, v___x_1559_);
                            crate::leanh::lean_dec_ref(v___x_1554_);
                            v_snd_1568_ = crate::leanh::lean_ctor_get(v___x_1567_, 1);
                            crate::leanh::lean_inc(v_snd_1568_);
                            crate::leanh::lean_dec_ref(v___x_1567_);
                            v___y_1544_ = v_snd_1568_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_1545_ = lean_array_size(v___y_1544_);
                v___x_1546_ = 0usize;
                v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1(v_sz_1545_, v___x_1546_, v___y_1544_);
                if crate::leanh::lean_obj_tag(v___x_1547_) == 0 {
                    v___x_1548_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg();
                    return v___x_1548_;
                } else {
                    v_val_1549_ = crate::leanh::lean_ctor_get(v___x_1547_, 0);
                    crate::leanh::lean_inc(v_val_1549_);
                    crate::leanh::lean_dec_ref_known(v___x_1547_, 1);
                    v_allVars_1550_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15;
                    v_sz_1551_ = lean_array_size(v_val_1549_);
                    v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2(v_val_1549_, v_sz_1551_, v___x_1546_, v_allVars_1550_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
                    crate::leanh::lean_dec(v_val_1549_);
                    return v___x_1552_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_getLetRecDeclsVars___boxed(
    mut v_letRecDecls_1569_: *mut crate::leanh::LeanObject,
    mut v_a_1570_: *mut crate::leanh::LeanObject,
    mut v_a_1571_: *mut crate::leanh::LeanObject,
    mut v_a_1572_: *mut crate::leanh::LeanObject,
    mut v_a_1573_: *mut crate::leanh::LeanObject,
    mut v_a_1574_: *mut crate::leanh::LeanObject,
    mut v_a_1575_: *mut crate::leanh::LeanObject,
    mut v_a_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1577_ = l_Lean_Elab_Do_getLetRecDeclsVars(
        v_letRecDecls_1569_,
        v_a_1570_,
        v_a_1571_,
        v_a_1572_,
        v_a_1573_,
        v_a_1574_,
        v_a_1575_,
    );
    crate::leanh::lean_dec(v_a_1575_);
    crate::leanh::lean_dec_ref(v_a_1574_);
    crate::leanh::lean_dec(v_a_1573_);
    crate::leanh::lean_dec_ref(v_a_1572_);
    crate::leanh::lean_dec(v_a_1571_);
    crate::leanh::lean_dec_ref(v_a_1570_);
    return v_res_1577_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2(
    mut v_sz_1578_: usize,
    mut v_i_1579_: usize,
    mut v_bs_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: u8 = 0;
    let mut v_v_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: usize = 0;
    let mut v___x_1586_: usize = 0;
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1581_ = lean_usize_dec_lt(v_i_1579_, v_sz_1578_);
                if v___x_1581_ == 0 {
                    return v_bs_1580_;
                } else {
                    v_v_1582_ = lean_array_uget(v_bs_1580_, v_i_1579_);
                    v___x_1583_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1584_ = lean_array_uset(v_bs_1580_, v_i_1579_, v___x_1583_);
                    v___x_1585_ = 1usize;
                    v___x_1586_ = lean_usize_add(v_i_1579_, v___x_1585_);
                    v___x_1587_ = lean_array_uset(v_bs_x27_1584_, v_i_1579_, v_v_1582_);
                    v_i_1579_ = v___x_1586_;
                    v_bs_1580_ = v___x_1587_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2___boxed(
    mut v_sz_1589_: *mut crate::leanh::LeanObject,
    mut v_i_1590_: *mut crate::leanh::LeanObject,
    mut v_bs_1591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1592_: usize = 0;
    let mut v_i_boxed_1593_: usize = 0;
    let mut v_res_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1592_ = crate::leanh::lean_unbox_usize(v_sz_1589_);
    crate::leanh::lean_dec(v_sz_1589_);
    v_i_boxed_1593_ = crate::leanh::lean_unbox_usize(v_i_1590_);
    crate::leanh::lean_dec(v_i_1590_);
    v_res_1594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2(v_sz_boxed_1592_, v_i_boxed_1593_, v_bs_1591_);
    return v_res_1594_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(
    mut v_sz_1595_: usize,
    mut v_i_1596_: usize,
    mut v_bs_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: u8 = 0;
    let mut v_v_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: usize = 0;
    let mut v___x_1603_: usize = 0;
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1598_ = lean_usize_dec_lt(v_i_1596_, v_sz_1595_);
                if v___x_1598_ == 0 {
                    return v_bs_1597_;
                } else {
                    v_v_1599_ = lean_array_uget(v_bs_1597_, v_i_1596_);
                    v___x_1600_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1601_ = lean_array_uset(v_bs_1597_, v_i_1596_, v___x_1600_);
                    v___x_1602_ = 1usize;
                    v___x_1603_ = lean_usize_add(v_i_1596_, v___x_1602_);
                    v___x_1604_ = lean_array_uset(v_bs_x27_1601_, v_i_1596_, v_v_1599_);
                    v_i_1596_ = v___x_1603_;
                    v_bs_1597_ = v___x_1604_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0___boxed(
    mut v_sz_1606_: *mut crate::leanh::LeanObject,
    mut v_i_1607_: *mut crate::leanh::LeanObject,
    mut v_bs_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1609_: usize = 0;
    let mut v_i_boxed_1610_: usize = 0;
    let mut v_res_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1609_ = crate::leanh::lean_unbox_usize(v_sz_1606_);
    crate::leanh::lean_dec(v_sz_1606_);
    v_i_boxed_1610_ = crate::leanh::lean_unbox_usize(v_i_1607_);
    crate::leanh::lean_dec(v_i_1607_);
    v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(v_sz_boxed_1609_, v_i_boxed_1610_, v_bs_1608_);
    return v_res_1611_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(
    mut v_as_1612_: *mut crate::leanh::LeanObject,
    mut v_i_1613_: usize,
    mut v_stop_1614_: usize,
    mut v_b_1615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: usize = 0;
    let mut v___x_1619_: usize = 0;
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1621_ = lean_usize_dec_eq(v_i_1613_, v_stop_1614_);
                if v___x_1621_ == 0 {
                    v___x_1622_ = lean_array_uget_borrowed(v_as_1612_, v_i_1613_);
                    v___x_1623_ = l_Lean_Syntax_isIdent(v___x_1622_);
                    if v___x_1623_ == 0 {
                        v___y_1617_ = v_b_1615_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_1622_);
                        v___x_1624_ = lean_array_push(v_b_1615_, v___x_1622_);
                        v___y_1617_ = v___x_1624_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1615_;
                }
            }
            1 => {
                v___x_1618_ = 1usize;
                v___x_1619_ = lean_usize_add(v_i_1613_, v___x_1618_);
                v_i_1613_ = v___x_1619_;
                v_b_1615_ = v___y_1617_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1___boxed(
    mut v_as_1625_: *mut crate::leanh::LeanObject,
    mut v_i_1626_: *mut crate::leanh::LeanObject,
    mut v_stop_1627_: *mut crate::leanh::LeanObject,
    mut v_b_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1629_: usize = 0;
    let mut v_stop_boxed_1630_: usize = 0;
    let mut v_res_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1629_ = crate::leanh::lean_unbox_usize(v_i_1626_);
    crate::leanh::lean_dec(v_i_1626_);
    v_stop_boxed_1630_ = crate::leanh::lean_unbox_usize(v_stop_1627_);
    crate::leanh::lean_dec(v_stop_1627_);
    v_res_1631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_as_1625_, v_i_boxed_1629_, v_stop_boxed_1630_, v_b_1628_);
    crate::leanh::lean_dec_ref(v_as_1625_);
    return v_res_1631_;
}
pub unsafe fn l_Lean_Elab_Do_getExprPatternVarsEx___redArg(
    mut v_exprPattern_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1647_: usize = 0;
    let mut v___y_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1651_: usize = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_x3f_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pvars_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: u8 = 0;
    let mut v___x_1672_: usize = 0;
    let mut v___x_1673_: usize = 0;
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: usize = 0;
    let mut v___x_1676_: usize = 0;
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1681_: usize = 0;
    let mut v___x_1682_: usize = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: u8 = 0;
    let mut v___x_1688_: usize = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: usize = 0;
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: u8 = 0;
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_x3f_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1654_ = l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1;
                crate::leanh::lean_inc(v_exprPattern_1638_);
                v___x_1655_ = l_Lean_Syntax_isOfKind(v_exprPattern_1638_, v___x_1654_);
                if v___x_1655_ == 0 {
                    crate::leanh::lean_dec(v_exprPattern_1638_);
                    v___x_1656_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg();
                    return v___x_1656_;
                } else {
                    v___x_1657_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1692_ = l_Lean_Syntax_getArg(v_exprPattern_1638_, v___x_1657_);
                    v___x_1693_ = l_Lean_Syntax_isNone(v___x_1692_);
                    if v___x_1693_ == 0 {
                        v___x_1694_ = crate::leanh::lean_unsigned_to_nat(2);
                        crate::leanh::lean_inc(v___x_1692_);
                        v___x_1695_ = l_Lean_Syntax_matchesNull(v___x_1692_, v___x_1694_);
                        if v___x_1695_ == 0 {
                            crate::leanh::lean_dec(v___x_1692_);
                            crate::leanh::lean_dec(v_exprPattern_1638_);
                            v___x_1696_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg();
                            return v___x_1696_;
                        } else {
                            v_var_x3f_1697_ = l_Lean_Syntax_getArg(v___x_1692_, v___x_1657_);
                            crate::leanh::lean_dec(v___x_1692_);
                            v___x_1698_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1698_, 0, v_var_x3f_1697_);
                            v_var_x3f_1659_ = v___x_1698_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1692_);
                        v___x_1699_ = crate::leanh::lean_box(0);
                        v_var_x3f_1659_ = v___x_1699_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_1642_ = lean_array_size(v___y_1641_);
                v___x_1643_ = 0usize;
                v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(v_sz_1642_, v___x_1643_, v___y_1641_);
                v___x_1645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1645_, 0, v___x_1644_);
                return v___x_1645_;
            }
            2 => {
                v___x_1650_ = l_Array_append___redArg(v___y_1648_, v___y_1649_);
                crate::leanh::lean_dec_ref(v___y_1649_);
                v_sz_1651_ = lean_array_size(v___x_1650_);
                v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(v_sz_1651_, v___y_1647_, v___x_1650_);
                v___x_1653_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1653_, 0, v___x_1652_);
                return v___x_1653_;
            }
            3 => {
                v___x_1660_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1661_ = l_Lean_Syntax_getArg(v_exprPattern_1638_, v___x_1660_);
                v___x_1662_ =
                    l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10;
                v___x_1663_ = l_Lean_Syntax_isOfKind(v___x_1661_, v___x_1662_);
                if v___x_1663_ == 0 {
                    crate::leanh::lean_dec(v_var_x3f_1659_);
                    crate::leanh::lean_dec(v_exprPattern_1638_);
                    v___x_1664_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___redArg();
                    return v___x_1664_;
                } else {
                    v___x_1665_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1666_ = l_Lean_Syntax_getArg(v_exprPattern_1638_, v___x_1665_);
                    crate::leanh::lean_dec(v_exprPattern_1638_);
                    v_pvars_1667_ = l_Lean_Syntax_getArgs(v___x_1666_);
                    crate::leanh::lean_dec(v___x_1666_);
                    if crate::leanh::lean_obj_tag(v_var_x3f_1659_) == 0 {
                        v___x_1668_ = lean_array_get_size(v_pvars_1667_);
                        v___x_1669_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15;
                        v___x_1670_ = lean_nat_dec_lt(v___x_1657_, v___x_1668_);
                        if v___x_1670_ == 0 {
                            crate::leanh::lean_dec_ref(v_pvars_1667_);
                            v___y_1641_ = v___x_1669_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1671_ = lean_nat_dec_le(v___x_1668_, v___x_1668_);
                            if v___x_1671_ == 0 {
                                if v___x_1670_ == 0 {
                                    crate::leanh::lean_dec_ref(v_pvars_1667_);
                                    v___y_1641_ = v___x_1669_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1672_ = 0usize;
                                    v___x_1673_ = lean_usize_of_nat(v___x_1668_);
                                    v___x_1674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_pvars_1667_, v___x_1672_, v___x_1673_, v___x_1669_);
                                    crate::leanh::lean_dec_ref(v_pvars_1667_);
                                    v___y_1641_ = v___x_1674_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_1675_ = 0usize;
                                v___x_1676_ = lean_usize_of_nat(v___x_1668_);
                                v___x_1677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_pvars_1667_, v___x_1675_, v___x_1676_, v___x_1669_);
                                crate::leanh::lean_dec_ref(v_pvars_1667_);
                                v___y_1641_ = v___x_1677_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_val_1678_ = crate::leanh::lean_ctor_get(v_var_x3f_1659_, 0);
                        crate::leanh::lean_inc(v_val_1678_);
                        crate::leanh::lean_dec_ref_known(v_var_x3f_1659_, 1);
                        v___x_1679_ = lean_mk_empty_array_with_capacity(v___x_1660_);
                        v___x_1680_ = lean_array_push(v___x_1679_, v_val_1678_);
                        v_sz_1681_ = lean_array_size(v___x_1680_);
                        v___x_1682_ = 0usize;
                        v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2(v_sz_1681_, v___x_1682_, v___x_1680_);
                        v___x_1684_ = lean_array_get_size(v_pvars_1667_);
                        v___x_1685_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15;
                        v___x_1686_ = lean_nat_dec_lt(v___x_1657_, v___x_1684_);
                        if v___x_1686_ == 0 {
                            crate::leanh::lean_dec_ref(v_pvars_1667_);
                            v___y_1647_ = v___x_1682_;
                            v___y_1648_ = v___x_1683_;
                            v___y_1649_ = v___x_1685_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1687_ = lean_nat_dec_le(v___x_1684_, v___x_1684_);
                            if v___x_1687_ == 0 {
                                if v___x_1686_ == 0 {
                                    crate::leanh::lean_dec_ref(v_pvars_1667_);
                                    v___y_1647_ = v___x_1682_;
                                    v___y_1648_ = v___x_1683_;
                                    v___y_1649_ = v___x_1685_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_1688_ = lean_usize_of_nat(v___x_1684_);
                                    v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_pvars_1667_, v___x_1682_, v___x_1688_, v___x_1685_);
                                    crate::leanh::lean_dec_ref(v_pvars_1667_);
                                    v___y_1647_ = v___x_1682_;
                                    v___y_1648_ = v___x_1683_;
                                    v___y_1649_ = v___x_1689_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_1690_ = lean_usize_of_nat(v___x_1684_);
                                v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_pvars_1667_, v___x_1682_, v___x_1690_, v___x_1685_);
                                crate::leanh::lean_dec_ref(v_pvars_1667_);
                                v___y_1647_ = v___x_1682_;
                                v___y_1648_ = v___x_1683_;
                                v___y_1649_ = v___x_1691_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_getExprPatternVarsEx___redArg___boxed(
    mut v_exprPattern_1700_: *mut crate::leanh::LeanObject,
    mut v_a_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lean_Elab_Do_getExprPatternVarsEx___redArg(v_exprPattern_1700_);
    return v_res_1702_;
}
pub unsafe fn l_Lean_Elab_Do_getExprPatternVarsEx(
    mut v_exprPattern_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
    mut v_a_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
    mut v_a_1708_: *mut crate::leanh::LeanObject,
    mut v_a_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Lean_Elab_Do_getExprPatternVarsEx___redArg(v_exprPattern_1703_);
    return v___x_1711_;
}
pub unsafe fn l_Lean_Elab_Do_getExprPatternVarsEx___boxed(
    mut v_exprPattern_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
    mut v_a_1714_: *mut crate::leanh::LeanObject,
    mut v_a_1715_: *mut crate::leanh::LeanObject,
    mut v_a_1716_: *mut crate::leanh::LeanObject,
    mut v_a_1717_: *mut crate::leanh::LeanObject,
    mut v_a_1718_: *mut crate::leanh::LeanObject,
    mut v_a_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lean_Elab_Do_getExprPatternVarsEx(
        v_exprPattern_1712_,
        v_a_1713_,
        v_a_1714_,
        v_a_1715_,
        v_a_1716_,
        v_a_1717_,
        v_a_1718_,
    );
    crate::leanh::lean_dec(v_a_1718_);
    crate::leanh::lean_dec_ref(v_a_1717_);
    crate::leanh::lean_dec(v_a_1716_);
    crate::leanh::lean_dec_ref(v_a_1715_);
    crate::leanh::lean_dec(v_a_1714_);
    crate::leanh::lean_dec_ref(v_a_1713_);
    return v_res_1720_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Do_PatternVar(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PatternVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Quotation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Do_PatternVar(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Do_PatternVar(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PatternVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Quotation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Do_PatternVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Do_PatternVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Do_PatternVar(builtin);
}

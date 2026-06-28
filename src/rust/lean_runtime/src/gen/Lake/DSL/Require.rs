// Lean compiler output
// Module: Lake.DSL.Require
// Imports: Lake.DSL.Syntax Lake.Config.Dependency
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_isNone,
    l_Lean_Syntax_mkNameLit, l_Lean_Syntax_mkStrLit, l_Lean_TSyntax_getId, l_Lean_mkCIdent,
    l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Macro_throwErrorAt___redArg,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lake::Config::Dependency::{
    initialize_Lake_Config_Dependency, runtime_initialize_Lake_Config_Dependency,
};
use crate::r#gen::Lake::DSL::DeclUtil::l_Lake_DSL_expandIdentOrStrAsIdent;
use crate::r#gen::Lake::DSL::Syntax::{
    initialize_Lake_DSL_Syntax, runtime_initialize_Lake_DSL_Syntax,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__3_value
) as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__3_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 111, 109, 101, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5_value) as *mut LeanObject,15308379890181982757 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__8_value
) as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__8_value) as *mut LeanObject,18184376426117065311 as *mut LeanObject] };
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5_value) as *mut LeanObject,4893146552088433753 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__10_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__12_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__12_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0_value) as *mut LeanObject,17416048715816169289 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2_value
) as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__8_value) as *mut LeanObject,18184376426117065311 as *mut LeanObject] };
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0_value) as *mut LeanObject,9480010471355609749 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        68, 101, 112, 101, 110, 100, 101, 110, 99, 121, 83, 114, 99, 46, 103, 105, 116, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        68, 101, 112, 101, 110, 100, 101, 110, 99, 121, 83, 114, 99, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3_value:
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
    m_data: [103, 105, 116, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3_value
) as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value
        ) as *mut LeanObject,
        10008488350202952551 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3_value
        ) as *mut LeanObject,
        7089029805941204291 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 102, 114, 111, 109, 32, 115, 121, 110,
        116, 97, 120, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__0_value:
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
    m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__1_value:
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
    m_data: [115, 117, 102, 102, 105, 120, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value:
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
    m_data: [44, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 99, 111, 112, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3_value
        ) as *mut LeanObject,
        14140964076517617371 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value:
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
    m_data: [118, 101, 114, 115, 105, 111, 110, 63, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6_value
        ) as *mut LeanObject,
        5707914067652744443 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9_value:
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
    m_data: [115, 114, 99, 63, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9_value
        ) as *mut LeanObject,
        16994205196275421986 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12_value:
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
    m_data: [111, 112, 116, 115, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12_value
        ) as *mut LeanObject,
        6757902475951869745 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value:
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
    m_data: [76, 97, 107, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value:
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
    m_data: [68, 83, 76, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 101, 112, 83, 112, 101, 99, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__17_value
        ) as *mut LeanObject,
        142218530785266487 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19_value:
    LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 114, 101, 113, 117, 105, 114, 101, 32,
        115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20_value:
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
    m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21_value:
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
    m_data: [64, 91, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23_value:
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
    m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24_value:
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
    m_data: [65, 116, 116, 114, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25_value:
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
    m_data: [115, 105, 109, 112, 108, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26_value:
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
    m_data: [112, 97, 99, 107, 97, 103, 101, 95, 100, 101, 112, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26_value
        ) as *mut LeanObject,
        4808916106510604781 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29_value:
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
    m_data: [93, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30_value:
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
    m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31_value:
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
    m_data: [100, 101, 102, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32_value:
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
    m_data: [100, 101, 99, 108, 73, 100, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34_value:
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
    m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35_value:
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
    m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36_value:
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
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37_value:
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
    m_data: [68, 101, 112, 101, 110, 100, 101, 110, 99, 121, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__37_value
        ) as *mut LeanObject,
        4262777339930964728 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41_value:
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
    m_data: [58, 61, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42_value:
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
        115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43_value:
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
        115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 76, 86, 97, 108, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44_value
        ) as *mut LeanObject,
        5949480926448383572 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 68, 101, 102, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48_value:
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
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49_value:
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
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50_value:
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
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51_value:
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
    m_data: [99, 104, 111, 105, 99, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__51_value
        ) as *mut LeanObject,
        11985596712582660667 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53_value:
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
    m_data: [116, 101, 114, 109, 123, 125, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__53_value
        ) as *mut LeanObject,
        5126085667538439468 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value:
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
    m_data: [123, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56_value:
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
    m_data: [125, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57_value:
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
    m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__57_value
        ) as *mut LeanObject,
        2026475204632980274 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value:
    LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__60_value
        ) as *mut LeanObject,
        5018042693327868416 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62_value:
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
    m_data: [111, 112, 116, 69, 108, 108, 105, 112, 115, 105, 115, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__62_value
        ) as *mut LeanObject,
        11580369617518985485 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value:
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
    m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_2:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value
        ) as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__65_value
        ) as *mut LeanObject,
        8497769072906204829 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_2:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value
        ) as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__67_value
        ) as *mut LeanObject,
        14557702332550915328 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [118, 101, 114, 83, 112, 101, 99, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__70_value
        ) as *mut LeanObject,
        3421776117942701061 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value:
    LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 118, 101, 114, 115, 105, 111, 110, 32,
        115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 97, 114, 101, 110, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__73_value
        ) as *mut LeanObject,
        7932075773091973500 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value:
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
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__75_value
        ) as *mut LeanObject,
        7306243862518720553 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77_value:
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
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78_value:
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
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__78_value
        ) as *mut LeanObject,
        9871775667037945883 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value:
    LeanStringObject<1> = LeanStringObject {
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
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81: *mut LeanObject =
    core::ptr::null_mut();
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value:
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
        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__82_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64_value
        ) as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value:
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
        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__84_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value:
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
        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__86_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value:
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
        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__88_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__89_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__87_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__90_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__85_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__91_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__83_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__92_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value:
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
    m_data: [116, 101, 114, 109, 95, 43, 43, 95, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__94_value
        ) as *mut LeanObject,
        1718176677342102874 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value:
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
    m_data: [115, 116, 114, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__96_value
        ) as *mut LeanObject,
        9232979286016572671 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98_value:
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
    m_data: [34, 103, 105, 116, 35, 34, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99_value:
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
    m_data: [43, 43, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value:
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
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 110, 97, 109, 101, 32, 115, 121, 110,
        116, 97, 120, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 101, 112, 78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__102_value
        ) as *mut LeanObject,
        13377777968340814859 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value:
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
    m_data: [102, 114, 111, 109, 83, 111, 117, 114, 99, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__104_value
        ) as *mut LeanObject,
        10611690220945862380 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [102, 114, 111, 109, 71, 105, 116, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__106_value
        ) as *mut LeanObject,
        8744503865935906362 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value:
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
    m_data: [102, 114, 111, 109, 80, 97, 116, 104, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__108_value
        ) as *mut LeanObject,
        10954861864498947928 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        68, 101, 112, 101, 110, 100, 101, 110, 99, 121, 83, 114, 99, 46, 112, 97, 116, 104, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value:
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
    m_data: [112, 97, 116, 104, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value
        ) as *mut LeanObject,
        10008488350202952551 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value
        ) as *mut LeanObject,
        196819483099133737 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2_value
        ) as *mut LeanObject,
        1677172229734045131 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__112_value
        ) as *mut LeanObject,
        8872534682319043741 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value:
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
        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__114_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__116_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__115_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__117_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value:
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
    m_data: [119, 105, 116, 104, 67, 108, 97, 117, 115, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__119_value
        ) as *mut LeanObject,
        15981276745742611006 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value:
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
    m_data: [102, 114, 111, 109, 67, 108, 97, 117, 115, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__121_value
        ) as *mut LeanObject,
        862063901515217772 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123_value:
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
    m_data: [118, 101, 114, 67, 108, 97, 117, 115, 101, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__123_value
        ) as *mut LeanObject,
        16691910745100808827 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0_value:
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
    m_data: [114, 101, 113, 117, 105, 114, 101, 68, 101, 99, 108, 0],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0_value
)
    as *mut LeanObject;
static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_0:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_1:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value:
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
            l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__0_value
        ) as *mut LeanObject,
        2294773639995807415 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2_value:
    LeanStringObject<31> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 114, 101, 113, 117, 105, 114, 101, 32,
        100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__0_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value) as *mut LeanObject,12997130533650095963 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value) as *mut LeanObject,11286550318989764116 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [82, 101, 113, 117, 105, 114, 101, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__4_value) as *mut LeanObject,4987058340917616870 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,9490582398683048687 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15_value) as *mut LeanObject,924247899294660915 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__16_value) as *mut LeanObject,15052578366153039388 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__9_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 120, 112, 97, 110, 100, 82, 101, 113, 117, 105, 114, 101, 68, 101, 99, 108, 0]};
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__9_value) as *mut LeanObject,2473406913613757794 as *mut LeanObject] };
static mut l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__10_value) as *mut LeanObject;
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0(
    mut v_toPure_1189_: *mut LeanObject,
    mut v_____do__lift_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1191_: u8 = 0;
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    v___x_1191_ = 0;
    v___x_1192_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1190_, v___x_1191_);
    v___x_1193_ = lean_apply_2(v_toPure_1189_, lean_box(0), v___x_1192_);
    return v___x_1193_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed(
    mut v_toPure_1194_: *mut LeanObject,
    mut v_____do__lift_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1196_: *mut LeanObject = core::ptr::null_mut();
    v_res_1196_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0(
        v_toPure_1194_,
        v_____do__lift_1195_,
    );
    lean_dec(v_____do__lift_1195_);
    return v_res_1196_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6()
-> *mut LeanObject {
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    v___x_1207_ =
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__5;
    v___x_1208_ = l_String_toRawSubstring_x27(v___x_1207_);
    return v___x_1208_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1(
    mut v_scp_1224_: *mut LeanObject,
    mut v_info_1225_: *mut LeanObject,
    mut v_val_1226_: *mut LeanObject,
    mut v_toPure_1227_: *mut LeanObject,
    mut v_quotCtx_1228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    v___x_1229_ =
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4;
    v___x_1230_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
    v___x_1231_ =
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7;
    v___x_1232_ = l_Lean_addMacroScope(v_quotCtx_1228_, v___x_1231_, v_scp_1224_);
    v___x_1233_ =
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11;
    lean_inc_n(v_info_1225_, 2);
    v___x_1234_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_1234_, 0, v_info_1225_);
    lean_ctor_set(v___x_1234_, 1, v___x_1230_);
    lean_ctor_set(v___x_1234_, 2, v___x_1232_);
    lean_ctor_set(v___x_1234_, 3, v___x_1233_);
    v___x_1235_ =
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13;
    v___x_1236_ = l_Lean_Syntax_node1(v_info_1225_, v___x_1235_, v_val_1226_);
    v___x_1237_ = l_Lean_Syntax_node2(v_info_1225_, v___x_1229_, v___x_1234_, v___x_1236_);
    v___x_1238_ = lean_apply_2(v_toPure_1227_, lean_box(0), v___x_1237_);
    return v___x_1238_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__2(
    mut v_info_1239_: *mut LeanObject,
    mut v_val_1240_: *mut LeanObject,
    mut v_toPure_1241_: *mut LeanObject,
    mut v_toBind_1242_: *mut LeanObject,
    mut v_getContext_1243_: *mut LeanObject,
    mut v_scp_1244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    v___f_1245_ = lean_alloc_closure(
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1245_, 0, v_scp_1244_);
    lean_closure_set(v___f_1245_, 1, v_info_1239_);
    lean_closure_set(v___f_1245_, 2, v_val_1240_);
    lean_closure_set(v___f_1245_, 3, v_toPure_1241_);
    v___x_1246_ = lean_apply_4(
        v_toBind_1242_,
        lean_box(0),
        lean_box(0),
        v_getContext_1243_,
        v___f_1245_,
    );
    return v___x_1246_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3(
    mut v_val_1247_: *mut LeanObject,
    mut v_toPure_1248_: *mut LeanObject,
    mut v_toBind_1249_: *mut LeanObject,
    mut v_getContext_1250_: *mut LeanObject,
    mut v_getCurrMacroScope_1251_: *mut LeanObject,
    mut v_info_1252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_1249_);
    v___f_1253_ = lean_alloc_closure(
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__2
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1253_, 0, v_info_1252_);
    lean_closure_set(v___f_1253_, 1, v_val_1247_);
    lean_closure_set(v___f_1253_, 2, v_toPure_1248_);
    lean_closure_set(v___f_1253_, 3, v_toBind_1249_);
    lean_closure_set(v___f_1253_, 4, v_getContext_1250_);
    v___x_1254_ = lean_apply_4(
        v_toBind_1249_,
        lean_box(0),
        lean_box(0),
        v_getCurrMacroScope_1251_,
        v___f_1253_,
    );
    return v___x_1254_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4(
    mut v_val_1255_: *mut LeanObject,
    mut v_withRef_1256_: *mut LeanObject,
    mut v___x_1257_: *mut LeanObject,
    mut v_oldRef_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1259_ = l_Lean_replaceRef(v_val_1255_, v_oldRef_1258_);
    v___x_1260_ = lean_apply_3(v_withRef_1256_, lean_box(0), v_ref_1259_, v___x_1257_);
    return v___x_1260_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4___boxed(
    mut v_val_1261_: *mut LeanObject,
    mut v_withRef_1262_: *mut LeanObject,
    mut v___x_1263_: *mut LeanObject,
    mut v_oldRef_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1265_: *mut LeanObject = core::ptr::null_mut();
    v_res_1265_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4(
        v_val_1261_,
        v_withRef_1262_,
        v___x_1263_,
        v_oldRef_1264_,
    );
    lean_dec(v_oldRef_1264_);
    lean_dec(v_val_1261_);
    return v_res_1265_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1()
-> *mut LeanObject {
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    v___x_1267_ =
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__0;
    v___x_1268_ = l_String_toRawSubstring_x27(v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6(
    mut v_scp_1280_: *mut LeanObject,
    mut v_info_1281_: *mut LeanObject,
    mut v_toPure_1282_: *mut LeanObject,
    mut v_quotCtx_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    v___x_1284_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
    v___x_1285_ =
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2;
    v___x_1286_ = l_Lean_addMacroScope(v_quotCtx_1283_, v___x_1285_, v_scp_1280_);
    v___x_1287_ =
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5;
    v___x_1288_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_1288_, 0, v_info_1281_);
    lean_ctor_set(v___x_1288_, 1, v___x_1284_);
    lean_ctor_set(v___x_1288_, 2, v___x_1286_);
    lean_ctor_set(v___x_1288_, 3, v___x_1287_);
    v___x_1289_ = lean_apply_2(v_toPure_1282_, lean_box(0), v___x_1288_);
    return v___x_1289_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__5(
    mut v_info_1290_: *mut LeanObject,
    mut v_toPure_1291_: *mut LeanObject,
    mut v_toBind_1292_: *mut LeanObject,
    mut v_getContext_1293_: *mut LeanObject,
    mut v_scp_1294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    v___f_1295_ = lean_alloc_closure(
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1295_, 0, v_scp_1294_);
    lean_closure_set(v___f_1295_, 1, v_info_1290_);
    lean_closure_set(v___f_1295_, 2, v_toPure_1291_);
    v___x_1296_ = lean_apply_4(
        v_toBind_1292_,
        lean_box(0),
        lean_box(0),
        v_getContext_1293_,
        v___f_1295_,
    );
    return v___x_1296_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7(
    mut v_toPure_1297_: *mut LeanObject,
    mut v_toBind_1298_: *mut LeanObject,
    mut v_getContext_1299_: *mut LeanObject,
    mut v_getCurrMacroScope_1300_: *mut LeanObject,
    mut v_info_1301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_1298_);
    v___f_1302_ = lean_alloc_closure(
        l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__5
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1302_, 0, v_info_1301_);
    lean_closure_set(v___f_1302_, 1, v_toPure_1297_);
    lean_closure_set(v___f_1302_, 2, v_toBind_1298_);
    lean_closure_set(v___f_1302_, 3, v_getContext_1299_);
    v___x_1303_ = lean_apply_4(
        v_toBind_1298_,
        lean_box(0),
        lean_box(0),
        v_getCurrMacroScope_1300_,
        v___f_1302_,
    );
    return v___x_1303_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg(
    mut v_inst_1304_: *mut LeanObject,
    mut v_inst_1305_: *mut LeanObject,
    mut v_term_x3f_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1307_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1307_ = lean_ctor_get(v_inst_1304_, 0);
    lean_inc_ref(v_toApplicative_1307_);
    if lean_obj_tag(v_term_x3f_1306_) == 1 {
        let mut v_toMonadRef_1308_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getCurrMacroScope_1309_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getContext_1310_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1311_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1312_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_1313_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getRef_1314_: *mut LeanObject = core::ptr::null_mut();
        let mut v_withRef_1315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
        v_toMonadRef_1308_ = lean_ctor_get(v_inst_1305_, 0);
        lean_inc_ref(v_toMonadRef_1308_);
        v_getCurrMacroScope_1309_ = lean_ctor_get(v_inst_1305_, 1);
        lean_inc(v_getCurrMacroScope_1309_);
        v_getContext_1310_ = lean_ctor_get(v_inst_1305_, 2);
        lean_inc(v_getContext_1310_);
        lean_dec_ref(v_inst_1305_);
        v_toBind_1311_ = lean_ctor_get(v_inst_1304_, 1);
        lean_inc_n(v_toBind_1311_, 4);
        lean_dec_ref(v_inst_1304_);
        v_toPure_1312_ = lean_ctor_get(v_toApplicative_1307_, 1);
        lean_inc_n(v_toPure_1312_, 2);
        lean_dec_ref(v_toApplicative_1307_);
        v_val_1313_ = lean_ctor_get(v_term_x3f_1306_, 0);
        lean_inc_n(v_val_1313_, 2);
        lean_dec_ref_known(v_term_x3f_1306_, 1);
        v_getRef_1314_ = lean_ctor_get(v_toMonadRef_1308_, 0);
        lean_inc_n(v_getRef_1314_, 2);
        v_withRef_1315_ = lean_ctor_get(v_toMonadRef_1308_, 1);
        lean_inc(v_withRef_1315_);
        lean_dec_ref(v_toMonadRef_1308_);
        v___f_1316_ = lean_alloc_closure(
            l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_1316_, 0, v_toPure_1312_);
        v___f_1317_ = lean_alloc_closure(
            l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_1317_, 0, v_val_1313_);
        lean_closure_set(v___f_1317_, 1, v_toPure_1312_);
        lean_closure_set(v___f_1317_, 2, v_toBind_1311_);
        lean_closure_set(v___f_1317_, 3, v_getContext_1310_);
        lean_closure_set(v___f_1317_, 4, v_getCurrMacroScope_1309_);
        v___x_1318_ = lean_apply_4(
            v_toBind_1311_,
            lean_box(0),
            lean_box(0),
            v_getRef_1314_,
            v___f_1316_,
        );
        v___x_1319_ = lean_apply_4(
            v_toBind_1311_,
            lean_box(0),
            lean_box(0),
            v___x_1318_,
            v___f_1317_,
        );
        v___f_1320_ = lean_alloc_closure(
            l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_1320_, 0, v_val_1313_);
        lean_closure_set(v___f_1320_, 1, v_withRef_1315_);
        lean_closure_set(v___f_1320_, 2, v___x_1319_);
        v___x_1321_ = lean_apply_4(
            v_toBind_1311_,
            lean_box(0),
            lean_box(0),
            v_getRef_1314_,
            v___f_1320_,
        );
        return v___x_1321_;
    } else {
        let mut v_toMonadRef_1322_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getCurrMacroScope_1323_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getContext_1324_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1325_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1326_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getRef_1327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_term_x3f_1306_);
        v_toMonadRef_1322_ = lean_ctor_get(v_inst_1305_, 0);
        lean_inc_ref(v_toMonadRef_1322_);
        v_getCurrMacroScope_1323_ = lean_ctor_get(v_inst_1305_, 1);
        lean_inc(v_getCurrMacroScope_1323_);
        v_getContext_1324_ = lean_ctor_get(v_inst_1305_, 2);
        lean_inc(v_getContext_1324_);
        lean_dec_ref(v_inst_1305_);
        v_toBind_1325_ = lean_ctor_get(v_inst_1304_, 1);
        lean_inc_n(v_toBind_1325_, 3);
        lean_dec_ref(v_inst_1304_);
        v_toPure_1326_ = lean_ctor_get(v_toApplicative_1307_, 1);
        lean_inc_n(v_toPure_1326_, 2);
        lean_dec_ref(v_toApplicative_1307_);
        v_getRef_1327_ = lean_ctor_get(v_toMonadRef_1322_, 0);
        lean_inc(v_getRef_1327_);
        lean_dec_ref(v_toMonadRef_1322_);
        v___f_1328_ = lean_alloc_closure(
            l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_1328_, 0, v_toPure_1326_);
        v___f_1329_ = lean_alloc_closure(
            l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1329_, 0, v_toPure_1326_);
        lean_closure_set(v___f_1329_, 1, v_toBind_1325_);
        lean_closure_set(v___f_1329_, 2, v_getContext_1324_);
        lean_closure_set(v___f_1329_, 3, v_getCurrMacroScope_1323_);
        v___x_1330_ = lean_apply_4(
            v_toBind_1325_,
            lean_box(0),
            lean_box(0),
            v_getRef_1327_,
            v___f_1328_,
        );
        v___x_1331_ = lean_apply_4(
            v_toBind_1325_,
            lean_box(0),
            lean_box(0),
            v___x_1330_,
            v___f_1329_,
        );
        return v___x_1331_;
    }
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm(
    mut v_m_1332_: *mut LeanObject,
    mut v_inst_1333_: *mut LeanObject,
    mut v_inst_1334_: *mut LeanObject,
    mut v_term_x3f_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1336_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1336_ = lean_ctor_get(v_inst_1333_, 0);
    lean_inc_ref(v_toApplicative_1336_);
    if lean_obj_tag(v_term_x3f_1335_) == 1 {
        let mut v_toMonadRef_1337_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getCurrMacroScope_1338_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getContext_1339_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1340_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1341_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_1342_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getRef_1343_: *mut LeanObject = core::ptr::null_mut();
        let mut v_withRef_1344_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
        v_toMonadRef_1337_ = lean_ctor_get(v_inst_1334_, 0);
        lean_inc_ref(v_toMonadRef_1337_);
        v_getCurrMacroScope_1338_ = lean_ctor_get(v_inst_1334_, 1);
        lean_inc(v_getCurrMacroScope_1338_);
        v_getContext_1339_ = lean_ctor_get(v_inst_1334_, 2);
        lean_inc(v_getContext_1339_);
        lean_dec_ref(v_inst_1334_);
        v_toBind_1340_ = lean_ctor_get(v_inst_1333_, 1);
        lean_inc_n(v_toBind_1340_, 4);
        lean_dec_ref(v_inst_1333_);
        v_toPure_1341_ = lean_ctor_get(v_toApplicative_1336_, 1);
        lean_inc_n(v_toPure_1341_, 2);
        lean_dec_ref(v_toApplicative_1336_);
        v_val_1342_ = lean_ctor_get(v_term_x3f_1335_, 0);
        lean_inc_n(v_val_1342_, 2);
        lean_dec_ref_known(v_term_x3f_1335_, 1);
        v_getRef_1343_ = lean_ctor_get(v_toMonadRef_1337_, 0);
        lean_inc_n(v_getRef_1343_, 2);
        v_withRef_1344_ = lean_ctor_get(v_toMonadRef_1337_, 1);
        lean_inc(v_withRef_1344_);
        lean_dec_ref(v_toMonadRef_1337_);
        v___f_1345_ = lean_alloc_closure(
            l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_1345_, 0, v_toPure_1341_);
        v___f_1346_ = lean_alloc_closure(
            l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__3
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_1346_, 0, v_val_1342_);
        lean_closure_set(v___f_1346_, 1, v_toPure_1341_);
        lean_closure_set(v___f_1346_, 2, v_toBind_1340_);
        lean_closure_set(v___f_1346_, 3, v_getContext_1339_);
        lean_closure_set(v___f_1346_, 4, v_getCurrMacroScope_1338_);
        v___x_1347_ = lean_apply_4(
            v_toBind_1340_,
            lean_box(0),
            lean_box(0),
            v_getRef_1343_,
            v___f_1345_,
        );
        v___x_1348_ = lean_apply_4(
            v_toBind_1340_,
            lean_box(0),
            lean_box(0),
            v___x_1347_,
            v___f_1346_,
        );
        v___f_1349_ = lean_alloc_closure(
            l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__4___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_1349_, 0, v_val_1342_);
        lean_closure_set(v___f_1349_, 1, v_withRef_1344_);
        lean_closure_set(v___f_1349_, 2, v___x_1348_);
        v___x_1350_ = lean_apply_4(
            v_toBind_1340_,
            lean_box(0),
            lean_box(0),
            v_getRef_1343_,
            v___f_1349_,
        );
        return v___x_1350_;
    } else {
        let mut v_toMonadRef_1351_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getCurrMacroScope_1352_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getContext_1353_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1354_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1355_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getRef_1356_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1357_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_term_x3f_1335_);
        v_toMonadRef_1351_ = lean_ctor_get(v_inst_1334_, 0);
        lean_inc_ref(v_toMonadRef_1351_);
        v_getCurrMacroScope_1352_ = lean_ctor_get(v_inst_1334_, 1);
        lean_inc(v_getCurrMacroScope_1352_);
        v_getContext_1353_ = lean_ctor_get(v_inst_1334_, 2);
        lean_inc(v_getContext_1353_);
        lean_dec_ref(v_inst_1334_);
        v_toBind_1354_ = lean_ctor_get(v_inst_1333_, 1);
        lean_inc_n(v_toBind_1354_, 3);
        lean_dec_ref(v_inst_1333_);
        v_toPure_1355_ = lean_ctor_get(v_toApplicative_1336_, 1);
        lean_inc_n(v_toPure_1355_, 2);
        lean_dec_ref(v_toApplicative_1336_);
        v_getRef_1356_ = lean_ctor_get(v_toMonadRef_1351_, 0);
        lean_inc(v_getRef_1356_);
        lean_dec_ref(v_toMonadRef_1351_);
        v___f_1357_ = lean_alloc_closure(
            l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_1357_, 0, v_toPure_1355_);
        v___f_1358_ = lean_alloc_closure(
            l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__7
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1358_, 0, v_toPure_1355_);
        lean_closure_set(v___f_1358_, 1, v_toBind_1354_);
        lean_closure_set(v___f_1358_, 2, v_getContext_1353_);
        lean_closure_set(v___f_1358_, 3, v_getCurrMacroScope_1352_);
        v___x_1359_ = lean_apply_4(
            v_toBind_1354_,
            lean_box(0),
            lean_box(0),
            v_getRef_1356_,
            v___f_1357_,
        );
        v___x_1360_ = lean_apply_4(
            v_toBind_1354_,
            lean_box(0),
            lean_box(0),
            v___x_1359_,
            v___f_1358_,
        );
        return v___x_1360_;
    }
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    v___x_1362_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__0;
    v___x_1363_ = l_String_toRawSubstring_x27(v___x_1362_);
    return v___x_1363_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(
    mut v___x_1370_: *mut LeanObject,
    mut v___x_1371_: *mut LeanObject,
    mut v_tk_1372_: *mut LeanObject,
    mut v___x_1373_: *mut LeanObject,
    mut v___x_1374_: *mut LeanObject,
    mut v___x_1375_: *mut LeanObject,
    mut v_val_1376_: *mut LeanObject,
    mut v___x_1377_: *mut LeanObject,
    mut v_x_1378_: *mut LeanObject,
    mut v_rev_x3f_1379_: *mut LeanObject,
    mut v___y_1380_: *mut LeanObject,
    mut v___y_1381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: u8 = 0;
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subDir_x3f_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: u8 = 0;
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subDir_x3f_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1461_ = l_Lean_Syntax_getArg(v___x_1373_, v___x_1374_);
                v___x_1462_ = l_Lean_Syntax_isNone(v___x_1461_);
                if v___x_1462_ == 0 {
                    lean_inc(v___x_1461_);
                    v___x_1463_ = l_Lean_Syntax_matchesNull(v___x_1461_, v___x_1375_);
                    if v___x_1463_ == 0 {
                        lean_dec(v___x_1461_);
                        lean_dec(v_rev_x3f_1379_);
                        lean_dec(v___x_1371_);
                        lean_dec_ref(v___x_1370_);
                        v___x_1464_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5;
                        v___x_1465_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_val_1376_,
                            v___x_1464_,
                            v___y_1380_,
                            v___y_1381_,
                        );
                        return v___x_1465_;
                    } else {
                        v_subDir_x3f_1466_ = l_Lean_Syntax_getArg(v___x_1461_, v___x_1377_);
                        lean_dec(v___x_1461_);
                        v___x_1467_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1467_, 0, v_subDir_x3f_1466_);
                        v_subDir_x3f_1436_ = v___x_1467_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1461_);
                    v___x_1468_ = lean_box(0);
                    v_subDir_x3f_1436_ = v___x_1468_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1389_ = 0;
                v___x_1390_ = l_Lean_SourceInfo_fromRef(v___y_1383_, v___x_1389_);
                lean_dec(v___y_1383_);
                v___x_1391_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4;
                v___x_1392_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__1);
                v___x_1393_ =
                    l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__2;
                v___x_1394_ =
                    l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__3;
                v___x_1395_ =
                    l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__4;
                v___x_1396_ = l_Lean_addMacroScope(v___y_1386_, v___x_1395_, v___y_1384_);
                v___x_1397_ = l_Lean_Name_mkStr3(v___x_1370_, v___x_1393_, v___x_1394_);
                v___x_1398_ = lean_box(0);
                lean_inc(v___x_1397_);
                v___x_1399_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1399_, 0, v___x_1397_);
                lean_ctor_set(v___x_1399_, 1, v___x_1398_);
                v___x_1400_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1400_, 0, v___x_1397_);
                v___x_1401_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1401_, 0, v___x_1400_);
                lean_ctor_set(v___x_1401_, 1, v___x_1398_);
                v___x_1402_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1402_, 0, v___x_1399_);
                lean_ctor_set(v___x_1402_, 1, v___x_1401_);
                lean_inc_n(v___x_1390_, 2);
                v___x_1403_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1403_, 0, v___x_1390_);
                lean_ctor_set(v___x_1403_, 1, v___x_1392_);
                lean_ctor_set(v___x_1403_, 2, v___x_1396_);
                lean_ctor_set(v___x_1403_, 3, v___x_1402_);
                v___x_1404_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13;
                v___x_1405_ = l_Lean_Syntax_node3(
                    v___x_1390_,
                    v___x_1404_,
                    v___x_1371_,
                    v___y_1385_,
                    v_a_1387_,
                );
                v___x_1406_ =
                    l_Lean_Syntax_node2(v___x_1390_, v___x_1391_, v___x_1403_, v___x_1405_);
                v___x_1407_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1407_, 0, v___x_1406_);
                lean_ctor_set(v___x_1407_, 1, v_a_1388_);
                return v___x_1407_;
            }
            2 => {
                if lean_obj_tag(v___y_1411_) == 1 {
                    v_val_1415_ = lean_ctor_get(v___y_1411_, 0);
                    lean_inc(v_val_1415_);
                    lean_dec_ref_known(v___y_1411_, 1);
                    v_ref_1416_ = l_Lean_replaceRef(v_val_1415_, v___y_1409_);
                    v___x_1417_ = 0;
                    v___x_1418_ = l_Lean_SourceInfo_fromRef(v_ref_1416_, v___x_1417_);
                    lean_dec(v_ref_1416_);
                    v___x_1419_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4;
                    v___x_1420_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
                    v___x_1421_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7;
                    lean_inc(v___y_1410_);
                    lean_inc(v___y_1412_);
                    v___x_1422_ = l_Lean_addMacroScope(v___y_1412_, v___x_1421_, v___y_1410_);
                    v___x_1423_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11;
                    lean_inc_n(v___x_1418_, 2);
                    v___x_1424_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_1424_, 0, v___x_1418_);
                    lean_ctor_set(v___x_1424_, 1, v___x_1420_);
                    lean_ctor_set(v___x_1424_, 2, v___x_1422_);
                    lean_ctor_set(v___x_1424_, 3, v___x_1423_);
                    v___x_1425_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13;
                    v___x_1426_ = l_Lean_Syntax_node1(v___x_1418_, v___x_1425_, v_val_1415_);
                    v___x_1427_ =
                        l_Lean_Syntax_node2(v___x_1418_, v___x_1419_, v___x_1424_, v___x_1426_);
                    v___y_1383_ = v___y_1409_;
                    v___y_1384_ = v___y_1410_;
                    v___y_1385_ = v_a_1413_;
                    v___y_1386_ = v___y_1412_;
                    v_a_1387_ = v___x_1427_;
                    v_a_1388_ = v_a_1414_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_1411_);
                    v___x_1428_ = 0;
                    v___x_1429_ = l_Lean_SourceInfo_fromRef(v___y_1409_, v___x_1428_);
                    v___x_1430_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
                    v___x_1431_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2;
                    lean_inc(v___y_1410_);
                    lean_inc(v___y_1412_);
                    v___x_1432_ = l_Lean_addMacroScope(v___y_1412_, v___x_1431_, v___y_1410_);
                    v___x_1433_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5;
                    v___x_1434_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_1434_, 0, v___x_1429_);
                    lean_ctor_set(v___x_1434_, 1, v___x_1430_);
                    lean_ctor_set(v___x_1434_, 2, v___x_1432_);
                    lean_ctor_set(v___x_1434_, 3, v___x_1433_);
                    v___y_1383_ = v___y_1409_;
                    v___y_1384_ = v___y_1410_;
                    v___y_1385_ = v_a_1413_;
                    v___y_1386_ = v___y_1412_;
                    v_a_1387_ = v___x_1434_;
                    v_a_1388_ = v_a_1414_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_quotContext_1437_ = lean_ctor_get(v___y_1380_, 1);
                v_currMacroScope_1438_ = lean_ctor_get(v___y_1380_, 2);
                v_ref_1439_ = lean_ctor_get(v___y_1380_, 5);
                v_ref_1440_ = l_Lean_replaceRef(v_tk_1372_, v_ref_1439_);
                if lean_obj_tag(v_rev_x3f_1379_) == 1 {
                    v_val_1441_ = lean_ctor_get(v_rev_x3f_1379_, 0);
                    lean_inc(v_val_1441_);
                    lean_dec_ref_known(v_rev_x3f_1379_, 1);
                    v_ref_1442_ = l_Lean_replaceRef(v_val_1441_, v_ref_1440_);
                    v___x_1443_ = 0;
                    v___x_1444_ = l_Lean_SourceInfo_fromRef(v_ref_1442_, v___x_1443_);
                    lean_dec(v_ref_1442_);
                    v___x_1445_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4;
                    v___x_1446_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
                    v___x_1447_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7;
                    lean_inc_n(v_currMacroScope_1438_, 2);
                    lean_inc_n(v_quotContext_1437_, 2);
                    v___x_1448_ = l_Lean_addMacroScope(
                        v_quotContext_1437_,
                        v___x_1447_,
                        v_currMacroScope_1438_,
                    );
                    v___x_1449_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11;
                    lean_inc_n(v___x_1444_, 2);
                    v___x_1450_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_1450_, 0, v___x_1444_);
                    lean_ctor_set(v___x_1450_, 1, v___x_1446_);
                    lean_ctor_set(v___x_1450_, 2, v___x_1448_);
                    lean_ctor_set(v___x_1450_, 3, v___x_1449_);
                    v___x_1451_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13;
                    v___x_1452_ = l_Lean_Syntax_node1(v___x_1444_, v___x_1451_, v_val_1441_);
                    v___x_1453_ =
                        l_Lean_Syntax_node2(v___x_1444_, v___x_1445_, v___x_1450_, v___x_1452_);
                    v___y_1409_ = v_ref_1440_;
                    v___y_1410_ = v_currMacroScope_1438_;
                    v___y_1411_ = v_subDir_x3f_1436_;
                    v___y_1412_ = v_quotContext_1437_;
                    v_a_1413_ = v___x_1453_;
                    v_a_1414_ = v___y_1381_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_rev_x3f_1379_);
                    v___x_1454_ = 0;
                    v___x_1455_ = l_Lean_SourceInfo_fromRef(v_ref_1440_, v___x_1454_);
                    v___x_1456_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
                    v___x_1457_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2;
                    lean_inc_n(v_currMacroScope_1438_, 2);
                    lean_inc_n(v_quotContext_1437_, 2);
                    v___x_1458_ = l_Lean_addMacroScope(
                        v_quotContext_1437_,
                        v___x_1457_,
                        v_currMacroScope_1438_,
                    );
                    v___x_1459_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5;
                    v___x_1460_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_1460_, 0, v___x_1455_);
                    lean_ctor_set(v___x_1460_, 1, v___x_1456_);
                    lean_ctor_set(v___x_1460_, 2, v___x_1458_);
                    lean_ctor_set(v___x_1460_, 3, v___x_1459_);
                    v___y_1409_ = v_ref_1440_;
                    v___y_1410_ = v_currMacroScope_1438_;
                    v___y_1411_ = v_subDir_x3f_1436_;
                    v___y_1412_ = v_quotContext_1437_;
                    v_a_1413_ = v___x_1460_;
                    v_a_1414_ = v___y_1381_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___boxed(
    mut v___x_1469_: *mut LeanObject,
    mut v___x_1470_: *mut LeanObject,
    mut v_tk_1471_: *mut LeanObject,
    mut v___x_1472_: *mut LeanObject,
    mut v___x_1473_: *mut LeanObject,
    mut v___x_1474_: *mut LeanObject,
    mut v_val_1475_: *mut LeanObject,
    mut v___x_1476_: *mut LeanObject,
    mut v_x_1477_: *mut LeanObject,
    mut v_rev_x3f_1478_: *mut LeanObject,
    mut v___y_1479_: *mut LeanObject,
    mut v___y_1480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1481_: *mut LeanObject = core::ptr::null_mut();
    v_res_1481_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(
        v___x_1469_,
        v___x_1470_,
        v_tk_1471_,
        v___x_1472_,
        v___x_1473_,
        v___x_1474_,
        v_val_1475_,
        v___x_1476_,
        v_x_1477_,
        v_rev_x3f_1478_,
        v___y_1479_,
        v___y_1480_,
    );
    lean_dec_ref(v___y_1479_);
    lean_dec(v___x_1476_);
    lean_dec(v_val_1475_);
    lean_dec(v___x_1474_);
    lean_dec(v___x_1473_);
    lean_dec(v___x_1472_);
    lean_dec(v_tk_1471_);
    return v_res_1481_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4()
-> *mut LeanObject {
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    v___x_1486_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__3;
    v___x_1487_ = l_String_toRawSubstring_x27(v___x_1486_);
    return v___x_1487_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7()
-> *mut LeanObject {
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    v___x_1491_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__6;
    v___x_1492_ = l_String_toRawSubstring_x27(v___x_1491_);
    return v___x_1492_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10()
-> *mut LeanObject {
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    v___x_1496_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__9;
    v___x_1497_ = l_String_toRawSubstring_x27(v___x_1496_);
    return v___x_1497_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13()
-> *mut LeanObject {
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    v___x_1501_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__12;
    v___x_1502_ = l_String_toRawSubstring_x27(v___x_1501_);
    return v___x_1502_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27()
-> *mut LeanObject {
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    v___x_1520_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__26;
    v___x_1521_ = l_String_toRawSubstring_x27(v___x_1520_);
    return v___x_1521_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39()
-> *mut LeanObject {
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    v___x_1537_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__38;
    v___x_1538_ = l_Lean_mkCIdent(v___x_1537_);
    return v___x_1538_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45()
-> *mut LeanObject {
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    v___x_1544_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__44;
    v___x_1545_ = l_String_toRawSubstring_x27(v___x_1544_);
    return v___x_1545_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59()
-> *mut LeanObject {
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    v___x_1566_ = l_Array_mkArray0(lean_box(0));
    return v___x_1566_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81()
-> *mut LeanObject {
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    v___x_1617_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80;
    v___x_1618_ = l_String_toRawSubstring_x27(v___x_1617_);
    return v___x_1618_;
}
pub unsafe fn _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111()
-> *mut LeanObject {
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    v___x_1682_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__110;
    v___x_1683_ = l_String_toRawSubstring_x27(v___x_1682_);
    return v___x_1683_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(
    mut v_stx_1718_: *mut LeanObject,
    mut v_doc_x3f_1719_: *mut LeanObject,
    mut v_a_1720_: *mut LeanObject,
    mut v_a_1721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ver_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: u8 = 0;
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: u8 = 0;
    let mut v_ref_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
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
    let mut v_quotContext_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: u8 = 0;
    let mut v___x_2140_: u8 = 0;
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: u8 = 0;
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_x3f_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: u8 = 0;
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2211_: u8 = 0;
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_x3f_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2223_: u8 = 0;
    let mut v___y_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_src_x3f_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: u8 = 0;
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_x3f_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ver_x3f_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: u8 = 0;
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: u8 = 0;
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_src_x3f_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: u8 = 0;
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: u8 = 0;
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ver_x3f_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1845_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__15;
                v___x_1846_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__18;
                lean_inc(v_stx_1718_);
                v___x_1847_ = l_Lean_Syntax_isOfKind(v_stx_1718_, v___x_1846_);
                if v___x_1847_ == 0 {
                    lean_dec(v_doc_x3f_1719_);
                    v___x_1848_ =
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19;
                    v___x_1849_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_stx_1718_,
                        v___x_1848_,
                        v_a_1720_,
                        v_a_1721_,
                    );
                    lean_dec(v_stx_1718_);
                    return v___x_1849_;
                } else {
                    v___x_1850_ = lean_unsigned_to_nat(0);
                    v___x_1851_ = l_Lean_Syntax_getArg(v_stx_1718_, v___x_1850_);
                    v___x_1852_ = lean_unsigned_to_nat(1);
                    v___x_2262_ = l_Lean_Syntax_getArg(v_stx_1718_, v___x_1852_);
                    v___x_2263_ = l_Lean_Syntax_isNone(v___x_2262_);
                    if v___x_2263_ == 0 {
                        lean_inc(v___x_2262_);
                        v___x_2264_ = l_Lean_Syntax_matchesNull(v___x_2262_, v___x_1852_);
                        if v___x_2264_ == 0 {
                            lean_dec(v___x_2262_);
                            lean_dec(v___x_1851_);
                            lean_dec(v_doc_x3f_1719_);
                            v___x_2265_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19;
                            v___x_2266_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_stx_1718_,
                                v___x_2265_,
                                v_a_1720_,
                                v_a_1721_,
                            );
                            lean_dec(v_stx_1718_);
                            return v___x_2266_;
                        } else {
                            v___x_2267_ = l_Lean_Syntax_getArg(v___x_2262_, v___x_1850_);
                            lean_dec(v___x_2262_);
                            v___x_2268_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__124;
                            lean_inc(v___x_2267_);
                            v___x_2269_ = l_Lean_Syntax_isOfKind(v___x_2267_, v___x_2268_);
                            if v___x_2269_ == 0 {
                                lean_dec(v___x_2267_);
                                lean_dec(v___x_1851_);
                                lean_dec(v_doc_x3f_1719_);
                                v___x_2270_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19;
                                v___x_2271_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_stx_1718_,
                                    v___x_2270_,
                                    v_a_1720_,
                                    v_a_1721_,
                                );
                                lean_dec(v_stx_1718_);
                                return v___x_2271_;
                            } else {
                                v_ver_x3f_2272_ = l_Lean_Syntax_getArg(v___x_2267_, v___x_1852_);
                                lean_dec(v___x_2267_);
                                v___x_2273_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2273_, 0, v_ver_x3f_2272_);
                                v_ver_x3f_2245_ = v___x_2273_;
                                v___y_2246_ = v_a_1720_;
                                v___y_2247_ = v_a_1721_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2262_);
                        v___x_2274_ = lean_box(0);
                        v_ver_x3f_2245_ = v___x_2274_;
                        v___y_2246_ = v_a_1720_;
                        v___y_2247_ = v_a_1721_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_n(v___y_1726_, 8);
                lean_inc(v___y_1735_);
                lean_inc_n(v___y_1737_, 9);
                v___x_1751_ = l_Lean_Syntax_node3(
                    v___y_1737_,
                    v___y_1727_,
                    v___y_1735_,
                    v___y_1726_,
                    v___y_1750_,
                );
                lean_inc_n(v___y_1743_, 2);
                v___x_1752_ = l_Lean_Syntax_node3(
                    v___y_1737_,
                    v___y_1743_,
                    v___y_1726_,
                    v___y_1726_,
                    v___x_1751_,
                );
                v___x_1753_ =
                    l_Lean_Syntax_node2(v___y_1737_, v___y_1738_, v___y_1723_, v___x_1752_);
                v___x_1754_ = lean_unsigned_to_nat(10);
                v___x_1755_ = lean_mk_empty_array_with_capacity(v___x_1754_);
                v___x_1756_ = lean_array_push(v___x_1755_, v___y_1734_);
                lean_inc_n(v___y_1733_, 4);
                v___x_1757_ = lean_array_push(v___x_1756_, v___y_1733_);
                v___x_1758_ = lean_array_push(v___x_1757_, v___y_1740_);
                v___x_1759_ = lean_array_push(v___x_1758_, v___y_1733_);
                v___x_1760_ = lean_array_push(v___x_1759_, v___y_1744_);
                v___x_1761_ = lean_array_push(v___x_1760_, v___y_1733_);
                v___x_1762_ = lean_array_push(v___x_1761_, v___y_1731_);
                v___x_1763_ = lean_array_push(v___x_1762_, v___y_1733_);
                v___x_1764_ = lean_array_push(v___x_1763_, v___x_1753_);
                v___x_1765_ = lean_array_push(v___x_1764_, v___y_1733_);
                v___x_1766_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1766_, 0, v___y_1737_);
                lean_ctor_set(v___x_1766_, 1, v___y_1743_);
                lean_ctor_set(v___x_1766_, 2, v___x_1765_);
                v___x_1767_ = l_Lean_Syntax_node1(v___y_1737_, v___y_1730_, v___x_1766_);
                v___x_1768_ = l_Lean_Syntax_node6(
                    v___y_1737_,
                    v___y_1747_,
                    v___y_1746_,
                    v___y_1726_,
                    v___x_1767_,
                    v___y_1729_,
                    v___y_1726_,
                    v___y_1724_,
                );
                v___x_1769_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__0;
                v___x_1770_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__1;
                lean_inc_ref(v___y_1745_);
                lean_inc_ref(v___y_1742_);
                v___x_1771_ =
                    l_Lean_Name_mkStr4(v___y_1742_, v___y_1745_, v___x_1769_, v___x_1770_);
                v___x_1772_ =
                    l_Lean_Syntax_node2(v___y_1737_, v___x_1771_, v___y_1726_, v___y_1726_);
                v___x_1773_ = l_Lean_Syntax_node4(
                    v___y_1737_,
                    v___y_1739_,
                    v___y_1735_,
                    v___x_1768_,
                    v___x_1772_,
                    v___y_1726_,
                );
                v___x_1774_ = l_Lean_Syntax_node5(
                    v___y_1737_,
                    v___y_1749_,
                    v___y_1736_,
                    v___y_1748_,
                    v___y_1725_,
                    v___x_1773_,
                    v___y_1726_,
                );
                lean_inc(v___y_1732_);
                v___x_1775_ =
                    l_Lean_Syntax_node2(v___y_1737_, v___y_1732_, v___y_1728_, v___x_1774_);
                v___x_1776_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1776_, 0, v___x_1775_);
                lean_ctor_set(v___x_1776_, 1, v___y_1741_);
                return v___x_1776_;
            }
            2 => {
                lean_inc_n(v___y_1784_, 16);
                lean_inc_n(v___y_1793_, 4);
                lean_inc_n(v___y_1785_, 4);
                lean_inc_n(v___y_1795_, 21);
                v___x_1810_ = l_Lean_Syntax_node3(
                    v___y_1795_,
                    v___y_1785_,
                    v___y_1793_,
                    v___y_1784_,
                    v___y_1809_,
                );
                lean_inc_n(v___y_1803_, 4);
                v___x_1811_ = l_Lean_Syntax_node3(
                    v___y_1795_,
                    v___y_1803_,
                    v___y_1784_,
                    v___y_1784_,
                    v___x_1810_,
                );
                lean_inc_n(v___y_1796_, 4);
                v___x_1812_ =
                    l_Lean_Syntax_node2(v___y_1795_, v___y_1796_, v___y_1800_, v___x_1811_);
                v___x_1813_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__2;
                v___x_1814_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1814_, 0, v___y_1795_);
                lean_ctor_set(v___x_1814_, 1, v___x_1813_);
                v___x_1815_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4_once
                    ),
                    _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__4,
                );
                v___x_1816_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__5;
                lean_inc_n(v___y_1778_, 3);
                lean_inc_n(v___y_1799_, 3);
                v___x_1817_ = l_Lean_addMacroScope(v___y_1799_, v___x_1816_, v___y_1778_);
                lean_inc_n(v___y_1791_, 3);
                v___x_1818_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1818_, 0, v___y_1795_);
                lean_ctor_set(v___x_1818_, 1, v___x_1815_);
                lean_ctor_set(v___x_1818_, 2, v___x_1817_);
                lean_ctor_set(v___x_1818_, 3, v___y_1791_);
                lean_inc_n(v___y_1798_, 3);
                v___x_1819_ =
                    l_Lean_Syntax_node2(v___y_1795_, v___y_1798_, v___x_1818_, v___y_1784_);
                v___x_1820_ = l_Lean_Syntax_node3(
                    v___y_1795_,
                    v___y_1785_,
                    v___y_1793_,
                    v___y_1784_,
                    v___y_1781_,
                );
                v___x_1821_ = l_Lean_Syntax_node3(
                    v___y_1795_,
                    v___y_1803_,
                    v___y_1784_,
                    v___y_1784_,
                    v___x_1820_,
                );
                v___x_1822_ =
                    l_Lean_Syntax_node2(v___y_1795_, v___y_1796_, v___x_1819_, v___x_1821_);
                v___x_1823_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7_once
                    ),
                    _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__7,
                );
                v___x_1824_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__8;
                v___x_1825_ = l_Lean_addMacroScope(v___y_1799_, v___x_1824_, v___y_1778_);
                v___x_1826_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1826_, 0, v___y_1795_);
                lean_ctor_set(v___x_1826_, 1, v___x_1823_);
                lean_ctor_set(v___x_1826_, 2, v___x_1825_);
                lean_ctor_set(v___x_1826_, 3, v___y_1791_);
                v___x_1827_ =
                    l_Lean_Syntax_node2(v___y_1795_, v___y_1798_, v___x_1826_, v___y_1784_);
                v___x_1828_ = l_Lean_Syntax_node3(
                    v___y_1795_,
                    v___y_1785_,
                    v___y_1793_,
                    v___y_1784_,
                    v___y_1783_,
                );
                v___x_1829_ = l_Lean_Syntax_node3(
                    v___y_1795_,
                    v___y_1803_,
                    v___y_1784_,
                    v___y_1784_,
                    v___x_1828_,
                );
                v___x_1830_ =
                    l_Lean_Syntax_node2(v___y_1795_, v___y_1796_, v___x_1827_, v___x_1829_);
                v___x_1831_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10_once
                    ),
                    _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__10,
                );
                v___x_1832_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__11;
                v___x_1833_ = l_Lean_addMacroScope(v___y_1799_, v___x_1832_, v___y_1778_);
                v___x_1834_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1834_, 0, v___y_1795_);
                lean_ctor_set(v___x_1834_, 1, v___x_1831_);
                lean_ctor_set(v___x_1834_, 2, v___x_1833_);
                lean_ctor_set(v___x_1834_, 3, v___y_1791_);
                v___x_1835_ =
                    l_Lean_Syntax_node2(v___y_1795_, v___y_1798_, v___x_1834_, v___y_1784_);
                v___x_1836_ = l_Lean_Syntax_node3(
                    v___y_1795_,
                    v___y_1785_,
                    v___y_1793_,
                    v___y_1784_,
                    v___y_1788_,
                );
                v___x_1837_ = l_Lean_Syntax_node3(
                    v___y_1795_,
                    v___y_1803_,
                    v___y_1784_,
                    v___y_1784_,
                    v___x_1836_,
                );
                v___x_1838_ =
                    l_Lean_Syntax_node2(v___y_1795_, v___y_1796_, v___x_1835_, v___x_1837_);
                v___x_1839_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13_once
                    ),
                    _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__13,
                );
                v___x_1840_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__14;
                v___x_1841_ = l_Lean_addMacroScope(v___y_1799_, v___x_1840_, v___y_1778_);
                v___x_1842_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1842_, 0, v___y_1795_);
                lean_ctor_set(v___x_1842_, 1, v___x_1839_);
                lean_ctor_set(v___x_1842_, 2, v___x_1841_);
                lean_ctor_set(v___x_1842_, 3, v___y_1791_);
                v___x_1843_ =
                    l_Lean_Syntax_node2(v___y_1795_, v___y_1798_, v___x_1842_, v___y_1784_);
                if lean_obj_tag(v___y_1790_) == 0 {
                    v___y_1723_ = v___x_1843_;
                    v___y_1724_ = v___y_1780_;
                    v___y_1725_ = v___y_1782_;
                    v___y_1726_ = v___y_1784_;
                    v___y_1727_ = v___y_1785_;
                    v___y_1728_ = v___y_1786_;
                    v___y_1729_ = v___y_1787_;
                    v___y_1730_ = v___y_1789_;
                    v___y_1731_ = v___x_1838_;
                    v___y_1732_ = v___y_1792_;
                    v___y_1733_ = v___x_1814_;
                    v___y_1734_ = v___x_1812_;
                    v___y_1735_ = v___y_1793_;
                    v___y_1736_ = v___y_1794_;
                    v___y_1737_ = v___y_1795_;
                    v___y_1738_ = v___y_1796_;
                    v___y_1739_ = v___y_1797_;
                    v___y_1740_ = v___x_1822_;
                    v___y_1741_ = v___y_1801_;
                    v___y_1742_ = v___y_1802_;
                    v___y_1743_ = v___y_1803_;
                    v___y_1744_ = v___x_1830_;
                    v___y_1745_ = v___y_1804_;
                    v___y_1746_ = v___y_1805_;
                    v___y_1747_ = v___y_1807_;
                    v___y_1748_ = v___y_1806_;
                    v___y_1749_ = v___y_1808_;
                    v___y_1750_ = v___y_1779_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_1779_);
                    v_val_1844_ = lean_ctor_get(v___y_1790_, 0);
                    lean_inc(v_val_1844_);
                    lean_dec_ref_known(v___y_1790_, 1);
                    v___y_1723_ = v___x_1843_;
                    v___y_1724_ = v___y_1780_;
                    v___y_1725_ = v___y_1782_;
                    v___y_1726_ = v___y_1784_;
                    v___y_1727_ = v___y_1785_;
                    v___y_1728_ = v___y_1786_;
                    v___y_1729_ = v___y_1787_;
                    v___y_1730_ = v___y_1789_;
                    v___y_1731_ = v___x_1838_;
                    v___y_1732_ = v___y_1792_;
                    v___y_1733_ = v___x_1814_;
                    v___y_1734_ = v___x_1812_;
                    v___y_1735_ = v___y_1793_;
                    v___y_1736_ = v___y_1794_;
                    v___y_1737_ = v___y_1795_;
                    v___y_1738_ = v___y_1796_;
                    v___y_1739_ = v___y_1797_;
                    v___y_1740_ = v___x_1822_;
                    v___y_1741_ = v___y_1801_;
                    v___y_1742_ = v___y_1802_;
                    v___y_1743_ = v___y_1803_;
                    v___y_1744_ = v___x_1830_;
                    v___y_1745_ = v___y_1804_;
                    v___y_1746_ = v___y_1805_;
                    v___y_1747_ = v___y_1807_;
                    v___y_1748_ = v___y_1806_;
                    v___y_1749_ = v___y_1808_;
                    v___y_1750_ = v_val_1844_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___y_1877_);
                v___x_1880_ = l_Array_append___redArg(v___y_1877_, v___y_1879_);
                lean_dec_ref(v___y_1879_);
                lean_inc_n(v___y_1873_, 5);
                lean_inc_n(v___y_1869_, 19);
                v___x_1881_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1881_, 0, v___y_1869_);
                lean_ctor_set(v___x_1881_, 1, v___y_1873_);
                lean_ctor_set(v___x_1881_, 2, v___x_1880_);
                v___x_1882_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__20;
                lean_inc_ref_n(v___y_1860_, 7);
                lean_inc_ref_n(v___y_1874_, 12);
                lean_inc_ref_n(v___y_1871_, 12);
                v___x_1883_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1860_, v___x_1882_);
                v___x_1884_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__21;
                v___x_1885_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1885_, 0, v___y_1869_);
                lean_ctor_set(v___x_1885_, 1, v___x_1884_);
                v___x_1886_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__22;
                v___x_1887_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1860_, v___x_1886_);
                v___x_1888_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__23;
                v___x_1889_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1860_, v___x_1888_);
                lean_inc_n(v___y_1859_, 9);
                v___x_1890_ = l_Lean_Syntax_node1(v___y_1869_, v___x_1889_, v___y_1859_);
                v___x_1891_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__24;
                v___x_1892_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__25;
                v___x_1893_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___x_1891_, v___x_1892_);
                v___x_1894_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27_once
                    ),
                    _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__27,
                );
                v___x_1895_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__28;
                lean_inc_n(v___y_1854_, 2);
                lean_inc_n(v___y_1870_, 2);
                v___x_1896_ = l_Lean_addMacroScope(v___y_1870_, v___x_1895_, v___y_1854_);
                v___x_1897_ = lean_box(0);
                v___x_1898_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1898_, 0, v___y_1869_);
                lean_ctor_set(v___x_1898_, 1, v___x_1894_);
                lean_ctor_set(v___x_1898_, 2, v___x_1896_);
                lean_ctor_set(v___x_1898_, 3, v___x_1897_);
                v___x_1899_ =
                    l_Lean_Syntax_node2(v___y_1869_, v___x_1893_, v___x_1898_, v___y_1859_);
                v___x_1900_ =
                    l_Lean_Syntax_node2(v___y_1869_, v___x_1887_, v___x_1890_, v___x_1899_);
                v___x_1901_ = l_Lean_Syntax_node1(v___y_1869_, v___y_1873_, v___x_1900_);
                v___x_1902_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__29;
                v___x_1903_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1903_, 0, v___y_1869_);
                lean_ctor_set(v___x_1903_, 1, v___x_1902_);
                v___x_1904_ = l_Lean_Syntax_node3(
                    v___y_1869_,
                    v___x_1883_,
                    v___x_1885_,
                    v___x_1901_,
                    v___x_1903_,
                );
                v___x_1905_ = l_Lean_Syntax_node1(v___y_1869_, v___y_1873_, v___x_1904_);
                lean_inc(v___y_1858_);
                v___x_1906_ = l_Lean_Syntax_node7(
                    v___y_1869_,
                    v___y_1858_,
                    v___x_1881_,
                    v___x_1905_,
                    v___y_1859_,
                    v___y_1859_,
                    v___y_1859_,
                    v___y_1859_,
                    v___y_1859_,
                );
                v___x_1907_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__30;
                lean_inc_ref_n(v___y_1878_, 4);
                v___x_1908_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1878_, v___x_1907_);
                v___x_1909_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__31;
                v___x_1910_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1910_, 0, v___y_1869_);
                lean_ctor_set(v___x_1910_, 1, v___x_1909_);
                v___x_1911_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__32;
                v___x_1912_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1878_, v___x_1911_);
                v___x_1913_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__33;
                v___x_1914_ = lean_box(2);
                v___x_1915_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1915_, 0, v___x_1914_);
                lean_ctor_set(v___x_1915_, 1, v___y_1873_);
                lean_ctor_set(v___x_1915_, 2, v___x_1913_);
                v___x_1916_ = lean_mk_empty_array_with_capacity(v___y_1868_);
                lean_inc(v___y_1867_);
                v___x_1917_ = lean_array_push(v___x_1916_, v___y_1867_);
                v___x_1918_ = lean_array_push(v___x_1917_, v___x_1915_);
                v___x_1919_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1919_, 0, v___x_1914_);
                lean_ctor_set(v___x_1919_, 1, v___x_1912_);
                lean_ctor_set(v___x_1919_, 2, v___x_1918_);
                v___x_1920_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__34;
                v___x_1921_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1878_, v___x_1920_);
                v___x_1922_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__35;
                v___x_1923_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1860_, v___x_1922_);
                v___x_1924_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__36;
                v___x_1925_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1925_, 0, v___y_1869_);
                lean_ctor_set(v___x_1925_, 1, v___x_1924_);
                v___x_1926_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39_once
                    ),
                    _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__39,
                );
                v___x_1927_ =
                    l_Lean_Syntax_node2(v___y_1869_, v___x_1923_, v___x_1925_, v___x_1926_);
                v___x_1928_ = l_Lean_Syntax_node1(v___y_1869_, v___y_1873_, v___x_1927_);
                v___x_1929_ =
                    l_Lean_Syntax_node2(v___y_1869_, v___x_1921_, v___y_1859_, v___x_1928_);
                v___x_1930_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__40;
                v___x_1931_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1878_, v___x_1930_);
                v___x_1932_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__41;
                v___x_1933_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1933_, 0, v___y_1869_);
                lean_ctor_set(v___x_1933_, 1, v___x_1932_);
                v___x_1934_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__42;
                v___x_1935_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1860_, v___x_1934_);
                v___x_1936_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__43;
                v___x_1937_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1860_, v___x_1936_);
                v___x_1938_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45_once
                    ),
                    _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__45,
                );
                v___x_1939_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__46;
                v___x_1940_ = l_Lean_addMacroScope(v___y_1870_, v___x_1939_, v___y_1854_);
                v___x_1941_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1941_, 0, v___y_1869_);
                lean_ctor_set(v___x_1941_, 1, v___x_1938_);
                lean_ctor_set(v___x_1941_, 2, v___x_1940_);
                lean_ctor_set(v___x_1941_, 3, v___x_1897_);
                lean_inc(v___x_1937_);
                v___x_1942_ =
                    l_Lean_Syntax_node2(v___y_1869_, v___x_1937_, v___x_1941_, v___y_1859_);
                v___x_1943_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__47;
                v___x_1944_ =
                    l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1860_, v___x_1943_);
                v___x_1945_ = l_Lean_TSyntax_getId(v___y_1867_);
                lean_dec(v___y_1867_);
                lean_inc(v___x_1945_);
                v___x_1946_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_1897_,
                    v___x_1945_,
                );
                if lean_obj_tag(v___x_1946_) == 0 {
                    v___x_1947_ = l_Lean_quoteNameMk(v___x_1945_);
                    v___y_1778_ = v___y_1854_;
                    v___y_1779_ = v___y_1855_;
                    v___y_1780_ = v___y_1856_;
                    v___y_1781_ = v___y_1857_;
                    v___y_1782_ = v___x_1929_;
                    v___y_1783_ = v___y_1861_;
                    v___y_1784_ = v___y_1859_;
                    v___y_1785_ = v___x_1944_;
                    v___y_1786_ = v___x_1906_;
                    v___y_1787_ = v___y_1862_;
                    v___y_1788_ = v___y_1863_;
                    v___y_1789_ = v___y_1864_;
                    v___y_1790_ = v___y_1865_;
                    v___y_1791_ = v___x_1897_;
                    v___y_1792_ = v___y_1866_;
                    v___y_1793_ = v___x_1933_;
                    v___y_1794_ = v___x_1910_;
                    v___y_1795_ = v___y_1869_;
                    v___y_1796_ = v___x_1935_;
                    v___y_1797_ = v___x_1931_;
                    v___y_1798_ = v___x_1937_;
                    v___y_1799_ = v___y_1870_;
                    v___y_1800_ = v___x_1942_;
                    v___y_1801_ = v___y_1872_;
                    v___y_1802_ = v___y_1871_;
                    v___y_1803_ = v___y_1873_;
                    v___y_1804_ = v___y_1874_;
                    v___y_1805_ = v___y_1875_;
                    v___y_1806_ = v___x_1919_;
                    v___y_1807_ = v___y_1876_;
                    v___y_1808_ = v___x_1908_;
                    v___y_1809_ = v___x_1947_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_1945_);
                    v_val_1948_ = lean_ctor_get(v___x_1946_, 0);
                    lean_inc(v_val_1948_);
                    lean_dec_ref_known(v___x_1946_, 1);
                    v___x_1949_ =
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__48;
                    lean_inc_ref(v___y_1860_);
                    lean_inc_ref(v___y_1874_);
                    lean_inc_ref(v___y_1871_);
                    v___x_1950_ =
                        l_Lean_Name_mkStr4(v___y_1871_, v___y_1874_, v___y_1860_, v___x_1949_);
                    v___x_1951_ =
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__49;
                    v___x_1952_ =
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__50;
                    v___x_1953_ = lean_string_intercalate(v___x_1952_, v_val_1948_);
                    v___x_1954_ = lean_string_append(v___x_1951_, v___x_1953_);
                    lean_dec_ref(v___x_1953_);
                    v___x_1955_ = l_Lean_Syntax_mkNameLit(v___x_1954_, v___x_1914_);
                    v___x_1956_ = lean_mk_empty_array_with_capacity(v___x_1852_);
                    v___x_1957_ = lean_array_push(v___x_1956_, v___x_1955_);
                    v___x_1958_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1958_, 0, v___x_1914_);
                    lean_ctor_set(v___x_1958_, 1, v___x_1950_);
                    lean_ctor_set(v___x_1958_, 2, v___x_1957_);
                    v___y_1778_ = v___y_1854_;
                    v___y_1779_ = v___y_1855_;
                    v___y_1780_ = v___y_1856_;
                    v___y_1781_ = v___y_1857_;
                    v___y_1782_ = v___x_1929_;
                    v___y_1783_ = v___y_1861_;
                    v___y_1784_ = v___y_1859_;
                    v___y_1785_ = v___x_1944_;
                    v___y_1786_ = v___x_1906_;
                    v___y_1787_ = v___y_1862_;
                    v___y_1788_ = v___y_1863_;
                    v___y_1789_ = v___y_1864_;
                    v___y_1790_ = v___y_1865_;
                    v___y_1791_ = v___x_1897_;
                    v___y_1792_ = v___y_1866_;
                    v___y_1793_ = v___x_1933_;
                    v___y_1794_ = v___x_1910_;
                    v___y_1795_ = v___y_1869_;
                    v___y_1796_ = v___x_1935_;
                    v___y_1797_ = v___x_1931_;
                    v___y_1798_ = v___x_1937_;
                    v___y_1799_ = v___y_1870_;
                    v___y_1800_ = v___x_1942_;
                    v___y_1801_ = v___y_1872_;
                    v___y_1802_ = v___y_1871_;
                    v___y_1803_ = v___y_1873_;
                    v___y_1804_ = v___y_1874_;
                    v___y_1805_ = v___y_1875_;
                    v___y_1806_ = v___x_1919_;
                    v___y_1807_ = v___y_1876_;
                    v___y_1808_ = v___x_1908_;
                    v___y_1809_ = v___x_1958_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_1970_ = 0;
                v___x_1971_ = l_Lean_SourceInfo_fromRef(v_ref_1967_, v___x_1970_);
                v___x_1972_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__52;
                v___x_1973_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__54;
                v___x_1974_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__55;
                lean_inc_n(v___x_1971_, 8);
                v___x_1975_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1975_, 0, v___x_1971_);
                lean_ctor_set(v___x_1975_, 1, v___x_1974_);
                v___x_1976_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__56;
                v___x_1977_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1977_, 0, v___x_1971_);
                lean_ctor_set(v___x_1977_, 1, v___x_1976_);
                lean_inc_ref_n(v___x_1977_, 2);
                lean_inc_ref_n(v___x_1975_, 2);
                v___x_1978_ =
                    l_Lean_Syntax_node2(v___x_1971_, v___x_1973_, v___x_1975_, v___x_1977_);
                v___x_1979_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__0;
                v___x_1980_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__1;
                v___x_1981_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__2;
                v___x_1982_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__58;
                v___x_1983_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13;
                v___x_1984_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59_once
                    ),
                    _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__59,
                );
                v___x_1985_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1985_, 0, v___x_1971_);
                lean_ctor_set(v___x_1985_, 1, v___x_1983_);
                lean_ctor_set(v___x_1985_, 2, v___x_1984_);
                v___x_1986_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__61;
                lean_inc_ref_n(v___x_1985_, 4);
                v___x_1987_ = l_Lean_Syntax_node1(v___x_1971_, v___x_1986_, v___x_1985_);
                v___x_1988_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__63;
                v___x_1989_ = l_Lean_Syntax_node1(v___x_1971_, v___x_1988_, v___x_1985_);
                lean_inc(v___x_1989_);
                v___x_1990_ = l_Lean_Syntax_node6(
                    v___x_1971_,
                    v___x_1982_,
                    v___x_1975_,
                    v___x_1985_,
                    v___x_1987_,
                    v___x_1989_,
                    v___x_1985_,
                    v___x_1977_,
                );
                v___x_1991_ =
                    l_Lean_Syntax_node2(v___x_1971_, v___x_1972_, v___x_1978_, v___x_1990_);
                v___x_1992_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__64;
                v___x_1993_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__66;
                v___x_1994_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__68;
                if lean_obj_tag(v_doc_x3f_1719_) == 1 {
                    v_val_1995_ = lean_ctor_get(v_doc_x3f_1719_, 0);
                    lean_inc(v_val_1995_);
                    lean_dec_ref_known(v_doc_x3f_1719_, 1);
                    v___x_1996_ = l_Array_mkArray1___redArg(v_val_1995_);
                    v___y_1854_ = v_currMacroScope_1966_;
                    v___y_1855_ = v___x_1991_;
                    v___y_1856_ = v___x_1977_;
                    v___y_1857_ = v___y_1962_;
                    v___y_1858_ = v___x_1994_;
                    v___y_1859_ = v___x_1985_;
                    v___y_1860_ = v___x_1981_;
                    v___y_1861_ = v___y_1964_;
                    v___y_1862_ = v___x_1989_;
                    v___y_1863_ = v_a_1968_;
                    v___y_1864_ = v___x_1986_;
                    v___y_1865_ = v___y_1960_;
                    v___y_1866_ = v___x_1993_;
                    v___y_1867_ = v___y_1961_;
                    v___y_1868_ = v___y_1963_;
                    v___y_1869_ = v___x_1971_;
                    v___y_1870_ = v_quotContext_1965_;
                    v___y_1871_ = v___x_1979_;
                    v___y_1872_ = v_a_1969_;
                    v___y_1873_ = v___x_1983_;
                    v___y_1874_ = v___x_1980_;
                    v___y_1875_ = v___x_1975_;
                    v___y_1876_ = v___x_1982_;
                    v___y_1877_ = v___x_1984_;
                    v___y_1878_ = v___x_1992_;
                    v___y_1879_ = v___x_1996_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_doc_x3f_1719_);
                    v___x_1997_ =
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__69;
                    v___y_1854_ = v_currMacroScope_1966_;
                    v___y_1855_ = v___x_1991_;
                    v___y_1856_ = v___x_1977_;
                    v___y_1857_ = v___y_1962_;
                    v___y_1858_ = v___x_1994_;
                    v___y_1859_ = v___x_1985_;
                    v___y_1860_ = v___x_1981_;
                    v___y_1861_ = v___y_1964_;
                    v___y_1862_ = v___x_1989_;
                    v___y_1863_ = v_a_1968_;
                    v___y_1864_ = v___x_1986_;
                    v___y_1865_ = v___y_1960_;
                    v___y_1866_ = v___x_1993_;
                    v___y_1867_ = v___y_1961_;
                    v___y_1868_ = v___y_1963_;
                    v___y_1869_ = v___x_1971_;
                    v___y_1870_ = v_quotContext_1965_;
                    v___y_1871_ = v___x_1979_;
                    v___y_1872_ = v_a_1969_;
                    v___y_1873_ = v___x_1983_;
                    v___y_1874_ = v___x_1980_;
                    v___y_1875_ = v___x_1975_;
                    v___y_1876_ = v___x_1982_;
                    v___y_1877_ = v___x_1984_;
                    v___y_1878_ = v___x_1992_;
                    v___y_1879_ = v___x_1997_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_2007_ = l_Lake_DSL_expandIdentOrStrAsIdent(v___y_2003_);
                if lean_obj_tag(v___y_2001_) == 1 {
                    v_val_2008_ = lean_ctor_get(v___y_2001_, 0);
                    lean_inc(v_val_2008_);
                    lean_dec_ref_known(v___y_2001_, 1);
                    v_quotContext_2009_ = lean_ctor_get(v___y_2005_, 1);
                    v_currMacroScope_2010_ = lean_ctor_get(v___y_2005_, 2);
                    v_ref_2011_ = lean_ctor_get(v___y_2005_, 5);
                    v_ref_2012_ = l_Lean_replaceRef(v_val_2008_, v_ref_2011_);
                    v___x_2013_ = 0;
                    v___x_2014_ = l_Lean_SourceInfo_fromRef(v_ref_2012_, v___x_2013_);
                    lean_dec(v_ref_2012_);
                    v___x_2015_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4;
                    v___x_2016_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
                    v___x_2017_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7;
                    lean_inc_n(v_currMacroScope_2010_, 2);
                    lean_inc_n(v_quotContext_2009_, 2);
                    v___x_2018_ = l_Lean_addMacroScope(
                        v_quotContext_2009_,
                        v___x_2017_,
                        v_currMacroScope_2010_,
                    );
                    v___x_2019_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11;
                    lean_inc_n(v___x_2014_, 2);
                    v___x_2020_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_2020_, 0, v___x_2014_);
                    lean_ctor_set(v___x_2020_, 1, v___x_2016_);
                    lean_ctor_set(v___x_2020_, 2, v___x_2018_);
                    lean_ctor_set(v___x_2020_, 3, v___x_2019_);
                    v___x_2021_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13;
                    v___x_2022_ = l_Lean_Syntax_node1(v___x_2014_, v___x_2021_, v_val_2008_);
                    v___x_2023_ =
                        l_Lean_Syntax_node2(v___x_2014_, v___x_2015_, v___x_2020_, v___x_2022_);
                    v___y_1960_ = v___y_1999_;
                    v___y_1961_ = v___x_2007_;
                    v___y_1962_ = v___y_2000_;
                    v___y_1963_ = v___y_2002_;
                    v___y_1964_ = v_ver_2004_;
                    v_quotContext_1965_ = v_quotContext_2009_;
                    v_currMacroScope_1966_ = v_currMacroScope_2010_;
                    v_ref_1967_ = v_ref_2011_;
                    v_a_1968_ = v___x_2023_;
                    v_a_1969_ = v___y_2006_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v___y_2001_);
                    v_quotContext_2024_ = lean_ctor_get(v___y_2005_, 1);
                    v_currMacroScope_2025_ = lean_ctor_get(v___y_2005_, 2);
                    v_ref_2026_ = lean_ctor_get(v___y_2005_, 5);
                    v___x_2027_ = 0;
                    v___x_2028_ = l_Lean_SourceInfo_fromRef(v_ref_2026_, v___x_2027_);
                    v___x_2029_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
                    v___x_2030_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2;
                    lean_inc_n(v_currMacroScope_2025_, 2);
                    lean_inc_n(v_quotContext_2024_, 2);
                    v___x_2031_ = l_Lean_addMacroScope(
                        v_quotContext_2024_,
                        v___x_2030_,
                        v_currMacroScope_2025_,
                    );
                    v___x_2032_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5;
                    v___x_2033_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_2033_, 0, v___x_2028_);
                    lean_ctor_set(v___x_2033_, 1, v___x_2029_);
                    lean_ctor_set(v___x_2033_, 2, v___x_2031_);
                    lean_ctor_set(v___x_2033_, 3, v___x_2032_);
                    v___y_1960_ = v___y_1999_;
                    v___y_1961_ = v___x_2007_;
                    v___y_1962_ = v___y_2000_;
                    v___y_1963_ = v___y_2002_;
                    v___y_1964_ = v_ver_2004_;
                    v_quotContext_1965_ = v_quotContext_2024_;
                    v_currMacroScope_1966_ = v_currMacroScope_2025_;
                    v_ref_1967_ = v_ref_2026_;
                    v_a_1968_ = v___x_2033_;
                    v_a_1969_ = v___y_2006_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if lean_obj_tag(v___y_2041_) == 0 {
                    v_a_2042_ = lean_ctor_get(v___y_2041_, 0);
                    lean_inc(v_a_2042_);
                    v_a_2043_ = lean_ctor_get(v___y_2041_, 1);
                    lean_inc(v_a_2043_);
                    lean_dec_ref_known(v___y_2041_, 2);
                    v___y_1999_ = v___y_2035_;
                    v___y_2000_ = v___y_2037_;
                    v___y_2001_ = v___y_2038_;
                    v___y_2002_ = v___y_2039_;
                    v___y_2003_ = v___y_2040_;
                    v_ver_2004_ = v_a_2042_;
                    v___y_2005_ = v___y_2036_;
                    v___y_2006_ = v_a_2043_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___y_2040_);
                    lean_dec(v___y_2038_);
                    lean_dec(v___y_2037_);
                    lean_dec(v___y_2035_);
                    lean_dec(v_doc_x3f_1719_);
                    return v___y_2041_;
                }
            }
            7 => {
                if lean_obj_tag(v___y_2050_) == 1 {
                    v_val_2053_ = lean_ctor_get(v___y_2050_, 0);
                    lean_inc_n(v_val_2053_, 2);
                    lean_dec_ref_known(v___y_2050_, 1);
                    v_methods_2054_ = lean_ctor_get(v___y_2047_, 0);
                    v_quotContext_2055_ = lean_ctor_get(v___y_2047_, 1);
                    v_currMacroScope_2056_ = lean_ctor_get(v___y_2047_, 2);
                    v_currRecDepth_2057_ = lean_ctor_get(v___y_2047_, 3);
                    v_maxRecDepth_2058_ = lean_ctor_get(v___y_2047_, 4);
                    v_ref_2059_ = lean_ctor_get(v___y_2047_, 5);
                    v___x_2060_ =
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__71;
                    v___x_2061_ = l_Lean_Syntax_isOfKind(v_val_2053_, v___x_2060_);
                    v_ref_2062_ = l_Lean_replaceRef(v_val_2053_, v_ref_2059_);
                    lean_inc(v_ref_2062_);
                    lean_inc(v_maxRecDepth_2058_);
                    lean_inc(v_currRecDepth_2057_);
                    lean_inc(v_currMacroScope_2056_);
                    lean_inc(v_quotContext_2055_);
                    lean_inc(v_methods_2054_);
                    v___x_2063_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v___x_2063_, 0, v_methods_2054_);
                    lean_ctor_set(v___x_2063_, 1, v_quotContext_2055_);
                    lean_ctor_set(v___x_2063_, 2, v_currMacroScope_2056_);
                    lean_ctor_set(v___x_2063_, 3, v_currRecDepth_2057_);
                    lean_ctor_set(v___x_2063_, 4, v_maxRecDepth_2058_);
                    lean_ctor_set(v___x_2063_, 5, v_ref_2062_);
                    if v___x_2061_ == 0 {
                        lean_dec(v_ref_2062_);
                        v___x_2064_ =
                            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72;
                        v___x_2065_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_val_2053_,
                            v___x_2064_,
                            v___x_2063_,
                            v___y_2046_,
                        );
                        lean_dec_ref_known(v___x_2063_, 6);
                        lean_dec(v_val_2053_);
                        v___y_2035_ = v___y_2045_;
                        v___y_2036_ = v___y_2047_;
                        v___y_2037_ = v___y_2052_;
                        v___y_2038_ = v___y_2048_;
                        v___y_2039_ = v___y_2049_;
                        v___y_2040_ = v___y_2051_;
                        v___y_2041_ = v___x_2065_;
                        state = 6;
                        continue;
                    } else {
                        v___x_2066_ = l_Lean_Syntax_getArg(v_val_2053_, v___x_1850_);
                        lean_inc(v___x_2066_);
                        v___x_2067_ = l_Lean_Syntax_matchesNull(v___x_2066_, v___x_1852_);
                        if v___x_2067_ == 0 {
                            v___x_2068_ = l_Lean_Syntax_matchesNull(v___x_2066_, v___x_1850_);
                            if v___x_2068_ == 0 {
                                lean_dec(v_ref_2062_);
                                v___x_2069_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__72;
                                v___x_2070_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_val_2053_,
                                    v___x_2069_,
                                    v___x_2063_,
                                    v___y_2046_,
                                );
                                lean_dec_ref_known(v___x_2063_, 6);
                                lean_dec(v_val_2053_);
                                v___y_2035_ = v___y_2045_;
                                v___y_2036_ = v___y_2047_;
                                v___y_2037_ = v___y_2052_;
                                v___y_2038_ = v___y_2048_;
                                v___y_2039_ = v___y_2049_;
                                v___y_2040_ = v___y_2051_;
                                v___y_2041_ = v___x_2070_;
                                state = 6;
                                continue;
                            } else {
                                lean_dec_ref_known(v___x_2063_, 6);
                                v___x_2071_ = l_Lean_Syntax_getArg(v_val_2053_, v___x_1852_);
                                lean_dec(v_val_2053_);
                                v___x_2072_ = l_Lean_SourceInfo_fromRef(v_ref_2062_, v___x_2067_);
                                lean_dec(v_ref_2062_);
                                v___x_2073_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4;
                                v___x_2074_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
                                v___x_2075_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7;
                                lean_inc(v_currMacroScope_2056_);
                                lean_inc(v_quotContext_2055_);
                                v___x_2076_ = l_Lean_addMacroScope(
                                    v_quotContext_2055_,
                                    v___x_2075_,
                                    v_currMacroScope_2056_,
                                );
                                v___x_2077_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11;
                                lean_inc_n(v___x_2072_, 2);
                                v___x_2078_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_2078_, 0, v___x_2072_);
                                lean_ctor_set(v___x_2078_, 1, v___x_2074_);
                                lean_ctor_set(v___x_2078_, 2, v___x_2076_);
                                lean_ctor_set(v___x_2078_, 3, v___x_2077_);
                                v___x_2079_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13;
                                v___x_2080_ =
                                    l_Lean_Syntax_node1(v___x_2072_, v___x_2079_, v___x_2071_);
                                v___x_2081_ = l_Lean_Syntax_node2(
                                    v___x_2072_,
                                    v___x_2073_,
                                    v___x_2078_,
                                    v___x_2080_,
                                );
                                v___y_1999_ = v___y_2045_;
                                v___y_2000_ = v___y_2052_;
                                v___y_2001_ = v___y_2048_;
                                v___y_2002_ = v___y_2049_;
                                v___y_2003_ = v___y_2051_;
                                v_ver_2004_ = v___x_2081_;
                                v___y_2005_ = v___y_2047_;
                                v___y_2006_ = v___y_2046_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_2066_);
                            lean_dec_ref_known(v___x_2063_, 6);
                            v___x_2082_ = l_Lean_Syntax_getArg(v_val_2053_, v___x_1852_);
                            lean_dec(v_val_2053_);
                            v___x_2083_ = 0;
                            v___x_2084_ = l_Lean_SourceInfo_fromRef(v_ref_2062_, v___x_2083_);
                            lean_dec(v_ref_2062_);
                            v___x_2085_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4;
                            v___x_2086_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__6);
                            v___x_2087_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__7;
                            lean_inc_n(v_currMacroScope_2056_, 2);
                            lean_inc_n(v_quotContext_2055_, 2);
                            v___x_2088_ = l_Lean_addMacroScope(
                                v_quotContext_2055_,
                                v___x_2087_,
                                v_currMacroScope_2056_,
                            );
                            v___x_2089_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__11;
                            lean_inc_n(v___x_2084_, 12);
                            v___x_2090_ = lean_alloc_ctor(3, 4, (0) as u32);
                            lean_ctor_set(v___x_2090_, 0, v___x_2084_);
                            lean_ctor_set(v___x_2090_, 1, v___x_2086_);
                            lean_ctor_set(v___x_2090_, 2, v___x_2088_);
                            lean_ctor_set(v___x_2090_, 3, v___x_2089_);
                            v___x_2091_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13;
                            v___x_2092_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__74;
                            v___x_2093_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__76;
                            v___x_2094_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__77;
                            v___x_2095_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_2095_, 0, v___x_2084_);
                            lean_ctor_set(v___x_2095_, 1, v___x_2094_);
                            v___x_2096_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__79;
                            v___x_2097_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__81);
                            v___x_2098_ = lean_box(0);
                            v___x_2099_ = l_Lean_addMacroScope(
                                v_quotContext_2055_,
                                v___x_2098_,
                                v_currMacroScope_2056_,
                            );
                            v___x_2100_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__93;
                            v___x_2101_ = lean_alloc_ctor(3, 4, (0) as u32);
                            lean_ctor_set(v___x_2101_, 0, v___x_2084_);
                            lean_ctor_set(v___x_2101_, 1, v___x_2097_);
                            lean_ctor_set(v___x_2101_, 2, v___x_2099_);
                            lean_ctor_set(v___x_2101_, 3, v___x_2100_);
                            v___x_2102_ =
                                l_Lean_Syntax_node1(v___x_2084_, v___x_2096_, v___x_2101_);
                            v___x_2103_ = l_Lean_Syntax_node2(
                                v___x_2084_,
                                v___x_2093_,
                                v___x_2095_,
                                v___x_2102_,
                            );
                            v___x_2104_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__95;
                            v___x_2105_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__97;
                            v___x_2106_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__98;
                            v___x_2107_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_2107_, 0, v___x_2084_);
                            lean_ctor_set(v___x_2107_, 1, v___x_2106_);
                            v___x_2108_ =
                                l_Lean_Syntax_node1(v___x_2084_, v___x_2105_, v___x_2107_);
                            v___x_2109_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__99;
                            v___x_2110_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_2110_, 0, v___x_2084_);
                            lean_ctor_set(v___x_2110_, 1, v___x_2109_);
                            v___x_2111_ = l_Lean_Syntax_node3(
                                v___x_2084_,
                                v___x_2104_,
                                v___x_2108_,
                                v___x_2110_,
                                v___x_2082_,
                            );
                            v___x_2112_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__100;
                            v___x_2113_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_2113_, 0, v___x_2084_);
                            lean_ctor_set(v___x_2113_, 1, v___x_2112_);
                            v___x_2114_ = l_Lean_Syntax_node3(
                                v___x_2084_,
                                v___x_2092_,
                                v___x_2103_,
                                v___x_2111_,
                                v___x_2113_,
                            );
                            v___x_2115_ =
                                l_Lean_Syntax_node1(v___x_2084_, v___x_2091_, v___x_2114_);
                            v___x_2116_ = l_Lean_Syntax_node2(
                                v___x_2084_,
                                v___x_2085_,
                                v___x_2090_,
                                v___x_2115_,
                            );
                            v___y_1999_ = v___y_2045_;
                            v___y_2000_ = v___y_2052_;
                            v___y_2001_ = v___y_2048_;
                            v___y_2002_ = v___y_2049_;
                            v___y_2003_ = v___y_2051_;
                            v_ver_2004_ = v___x_2116_;
                            v___y_2005_ = v___y_2047_;
                            v___y_2006_ = v___y_2046_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2050_);
                    v_quotContext_2117_ = lean_ctor_get(v___y_2047_, 1);
                    v_currMacroScope_2118_ = lean_ctor_get(v___y_2047_, 2);
                    v_ref_2119_ = lean_ctor_get(v___y_2047_, 5);
                    v___x_2120_ = 0;
                    v___x_2121_ = l_Lean_SourceInfo_fromRef(v_ref_2119_, v___x_2120_);
                    v___x_2122_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__1);
                    v___x_2123_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__2;
                    lean_inc(v_currMacroScope_2118_);
                    lean_inc(v_quotContext_2117_);
                    v___x_2124_ = l_Lean_addMacroScope(
                        v_quotContext_2117_,
                        v___x_2123_,
                        v_currMacroScope_2118_,
                    );
                    v___x_2125_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__6___closed__5;
                    v___x_2126_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_2126_, 0, v___x_2121_);
                    lean_ctor_set(v___x_2126_, 1, v___x_2122_);
                    lean_ctor_set(v___x_2126_, 2, v___x_2124_);
                    lean_ctor_set(v___x_2126_, 3, v___x_2125_);
                    v___y_1999_ = v___y_2045_;
                    v___y_2000_ = v___y_2052_;
                    v___y_2001_ = v___y_2048_;
                    v___y_2002_ = v___y_2049_;
                    v___y_2003_ = v___y_2051_;
                    v_ver_2004_ = v___x_2126_;
                    v___y_2005_ = v___y_2047_;
                    v___y_2006_ = v___y_2046_;
                    state = 5;
                    continue;
                }
            }
            8 => {
                lean_inc(v___x_1851_);
                v___x_2135_ = l_Lean_Syntax_isOfKind(v___x_1851_, v___y_2132_);
                if v___x_2135_ == 0 {
                    lean_dec(v_a_2133_);
                    lean_dec(v___y_2131_);
                    lean_dec(v___y_2128_);
                    lean_dec(v_doc_x3f_1719_);
                    v___x_2136_ =
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101;
                    v___x_2137_ = l_Lean_Macro_throwErrorAt___redArg(
                        v___x_1851_,
                        v___x_2136_,
                        v___y_2129_,
                        v_a_2134_,
                    );
                    lean_dec(v___x_1851_);
                    return v___x_2137_;
                } else {
                    v___x_2138_ = l_Lean_Syntax_getArg(v___x_1851_, v___x_1850_);
                    v___x_2139_ = l_Lean_Syntax_isNone(v___x_2138_);
                    if v___x_2139_ == 0 {
                        lean_inc(v___x_2138_);
                        v___x_2140_ = l_Lean_Syntax_matchesNull(v___x_2138_, v___y_2130_);
                        if v___x_2140_ == 0 {
                            lean_dec(v___x_2138_);
                            lean_dec(v_a_2133_);
                            lean_dec(v___y_2131_);
                            lean_dec(v___y_2128_);
                            lean_dec(v_doc_x3f_1719_);
                            v___x_2141_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__101;
                            v___x_2142_ = l_Lean_Macro_throwErrorAt___redArg(
                                v___x_1851_,
                                v___x_2141_,
                                v___y_2129_,
                                v_a_2134_,
                            );
                            lean_dec(v___x_1851_);
                            return v___x_2142_;
                        } else {
                            v___x_2143_ = l_Lean_Syntax_getArg(v___x_2138_, v___x_1850_);
                            lean_dec(v___x_2138_);
                            v___x_2144_ = l_Lean_Syntax_getArg(v___x_1851_, v___x_1852_);
                            lean_dec(v___x_1851_);
                            v___y_2045_ = v___y_2128_;
                            v___y_2046_ = v_a_2134_;
                            v___y_2047_ = v___y_2129_;
                            v___y_2048_ = v_a_2133_;
                            v___y_2049_ = v___y_2130_;
                            v___y_2050_ = v___y_2131_;
                            v___y_2051_ = v___x_2144_;
                            v___y_2052_ = v___x_2143_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2138_);
                        v___x_2145_ = l_Lean_Syntax_getArg(v___x_1851_, v___x_1852_);
                        v___x_2146_ =
                            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__80;
                        v___x_2147_ = 0;
                        v___x_2148_ = l_Lean_SourceInfo_fromRef(v___x_1851_, v___x_2147_);
                        lean_dec(v___x_1851_);
                        v___x_2149_ = l_Lean_Syntax_mkStrLit(v___x_2146_, v___x_2148_);
                        v___y_2045_ = v___y_2128_;
                        v___y_2046_ = v_a_2134_;
                        v___y_2047_ = v___y_2129_;
                        v___y_2048_ = v_a_2133_;
                        v___y_2049_ = v___y_2130_;
                        v___y_2050_ = v___y_2131_;
                        v___y_2051_ = v___x_2145_;
                        v___y_2052_ = v___x_2149_;
                        state = 7;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2158_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2158_, 0, v_a_2156_);
                v___y_2128_ = v___y_2151_;
                v___y_2129_ = v___y_2153_;
                v___y_2130_ = v___y_2152_;
                v___y_2131_ = v___y_2154_;
                v___y_2132_ = v___y_2155_;
                v_a_2133_ = v___x_2158_;
                v_a_2134_ = v_a_2157_;
                state = 8;
                continue;
            }
            10 => {
                if lean_obj_tag(v___y_2165_) == 0 {
                    v_a_2166_ = lean_ctor_get(v___y_2165_, 0);
                    lean_inc(v_a_2166_);
                    v_a_2167_ = lean_ctor_get(v___y_2165_, 1);
                    lean_inc(v_a_2167_);
                    lean_dec_ref_known(v___y_2165_, 2);
                    v___y_2151_ = v___y_2160_;
                    v___y_2152_ = v___y_2162_;
                    v___y_2153_ = v___y_2161_;
                    v___y_2154_ = v___y_2163_;
                    v___y_2155_ = v___y_2164_;
                    v_a_2156_ = v_a_2166_;
                    v_a_2157_ = v_a_2167_;
                    state = 9;
                    continue;
                } else {
                    lean_dec(v___y_2163_);
                    lean_dec(v___y_2160_);
                    lean_dec(v___x_1851_);
                    lean_dec(v_doc_x3f_1719_);
                    return v___y_2165_;
                }
            }
            11 => {
                v___x_2176_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__103;
                if lean_obj_tag(v___y_2174_) == 0 {
                    v___y_2128_ = v_opts_x3f_2175_;
                    v___y_2129_ = v___y_2170_;
                    v___y_2130_ = v___y_2172_;
                    v___y_2131_ = v___y_2173_;
                    v___y_2132_ = v___x_2176_;
                    v_a_2133_ = v___y_2174_;
                    v_a_2134_ = v___y_2169_;
                    state = 8;
                    continue;
                } else {
                    v_val_2177_ = lean_ctor_get(v___y_2174_, 0);
                    v_isSharedCheck_2223_ = (!lean_is_exclusive(v___y_2174_)) as u8;
                    if v_isSharedCheck_2223_ == 0 {
                        v___x_2179_ = v___y_2174_;
                        v_isShared_2180_ = v_isSharedCheck_2223_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_val_2177_);
                        lean_dec(v___y_2174_);
                        v___x_2179_ = lean_box(0);
                        v_isShared_2180_ = v_isSharedCheck_2223_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                v___x_2181_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__105;
                lean_inc(v_val_2177_);
                v___x_2182_ = l_Lean_Syntax_isOfKind(v_val_2177_, v___x_2181_);
                if v___x_2182_ == 0 {
                    lean_del_object(v___x_2179_);
                    v___x_2183_ =
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5;
                    v___x_2184_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_val_2177_,
                        v___x_2183_,
                        v___y_2170_,
                        v___y_2169_,
                    );
                    lean_dec(v_val_2177_);
                    v___y_2160_ = v_opts_x3f_2175_;
                    v___y_2161_ = v___y_2170_;
                    v___y_2162_ = v___y_2172_;
                    v___y_2163_ = v___y_2173_;
                    v___y_2164_ = v___x_2176_;
                    v___y_2165_ = v___x_2184_;
                    state = 10;
                    continue;
                } else {
                    v___x_2185_ = l_Lean_Syntax_getArg(v_val_2177_, v___x_1850_);
                    v___x_2186_ =
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__107;
                    lean_inc(v___x_2185_);
                    v___x_2187_ = l_Lean_Syntax_isOfKind(v___x_2185_, v___x_2186_);
                    if v___x_2187_ == 0 {
                        lean_del_object(v___x_2179_);
                        v___x_2188_ =
                            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__109;
                        lean_inc(v___x_2185_);
                        v___x_2189_ = l_Lean_Syntax_isOfKind(v___x_2185_, v___x_2188_);
                        if v___x_2189_ == 0 {
                            lean_dec(v___x_2185_);
                            v___x_2190_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5;
                            v___x_2191_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_val_2177_,
                                v___x_2190_,
                                v___y_2170_,
                                v___y_2169_,
                            );
                            lean_dec(v_val_2177_);
                            v___y_2160_ = v_opts_x3f_2175_;
                            v___y_2161_ = v___y_2170_;
                            v___y_2162_ = v___y_2172_;
                            v___y_2163_ = v___y_2173_;
                            v___y_2164_ = v___x_2176_;
                            v___y_2165_ = v___x_2191_;
                            state = 10;
                            continue;
                        } else {
                            v_quotContext_2192_ = lean_ctor_get(v___y_2170_, 1);
                            v_currMacroScope_2193_ = lean_ctor_get(v___y_2170_, 2);
                            v_ref_2194_ = lean_ctor_get(v___y_2170_, 5);
                            v___x_2195_ = l_Lean_Syntax_getArg(v___x_2185_, v___x_1850_);
                            lean_dec(v___x_2185_);
                            v_ref_2196_ = l_Lean_replaceRef(v_val_2177_, v_ref_2194_);
                            lean_dec(v_val_2177_);
                            v___x_2197_ = l_Lean_SourceInfo_fromRef(v_ref_2196_, v___x_2187_);
                            lean_dec(v_ref_2196_);
                            v___x_2198_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__4;
                            v___x_2199_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111), core::ptr::addr_of_mut!(l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111_once), _init_l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__111);
                            v___x_2200_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__113;
                            lean_inc(v_currMacroScope_2193_);
                            lean_inc(v_quotContext_2192_);
                            v___x_2201_ = l_Lean_addMacroScope(
                                v_quotContext_2192_,
                                v___x_2200_,
                                v_currMacroScope_2193_,
                            );
                            v___x_2202_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__118;
                            lean_inc_n(v___x_2197_, 2);
                            v___x_2203_ = lean_alloc_ctor(3, 4, (0) as u32);
                            lean_ctor_set(v___x_2203_, 0, v___x_2197_);
                            lean_ctor_set(v___x_2203_, 1, v___x_2199_);
                            lean_ctor_set(v___x_2203_, 2, v___x_2201_);
                            lean_ctor_set(v___x_2203_, 3, v___x_2202_);
                            v___x_2204_ = l___private_Lake_DSL_Require_0__Lake_DSL_quoteOptTerm___redArg___lam__1___closed__13;
                            v___x_2205_ =
                                l_Lean_Syntax_node1(v___x_2197_, v___x_2204_, v___x_2195_);
                            v___x_2206_ = l_Lean_Syntax_node2(
                                v___x_2197_,
                                v___x_2198_,
                                v___x_2203_,
                                v___x_2205_,
                            );
                            v___y_2151_ = v_opts_x3f_2175_;
                            v___y_2152_ = v___y_2172_;
                            v___y_2153_ = v___y_2170_;
                            v___y_2154_ = v___y_2173_;
                            v___y_2155_ = v___x_2176_;
                            v_a_2156_ = v___x_2206_;
                            v_a_2157_ = v___y_2169_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_tk_2207_ = l_Lean_Syntax_getArg(v___x_2185_, v___x_1850_);
                        v___x_2208_ = l_Lean_Syntax_getArg(v___x_2185_, v___x_1852_);
                        v___x_2209_ = l_Lean_Syntax_getArg(v___x_2185_, v___y_2172_);
                        v___x_2210_ = l_Lean_Syntax_isNone(v___x_2209_);
                        if v___x_2210_ == 0 {
                            lean_inc(v___x_2209_);
                            v___x_2211_ = l_Lean_Syntax_matchesNull(v___x_2209_, v___y_2172_);
                            if v___x_2211_ == 0 {
                                lean_dec(v___x_2209_);
                                lean_dec(v___x_2208_);
                                lean_dec(v_tk_2207_);
                                lean_dec(v___x_2185_);
                                lean_del_object(v___x_2179_);
                                v___x_2212_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0___closed__5;
                                v___x_2213_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_val_2177_,
                                    v___x_2212_,
                                    v___y_2170_,
                                    v___y_2169_,
                                );
                                lean_dec(v_val_2177_);
                                v___y_2160_ = v_opts_x3f_2175_;
                                v___y_2161_ = v___y_2170_;
                                v___y_2162_ = v___y_2172_;
                                v___y_2163_ = v___y_2173_;
                                v___y_2164_ = v___x_2176_;
                                v___y_2165_ = v___x_2213_;
                                state = 10;
                                continue;
                            } else {
                                v_rev_x3f_2214_ = l_Lean_Syntax_getArg(v___x_2209_, v___x_1852_);
                                lean_dec(v___x_2209_);
                                v___x_2215_ = lean_box(0);
                                if v_isShared_2180_ == 0 {
                                    lean_ctor_set(v___x_2179_, 0, v_rev_x3f_2214_);
                                    v___x_2217_ = v___x_2179_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_rev_x3f_2214_);
                                    v___x_2217_ = v_reuseFailAlloc_2219_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2209_);
                            lean_del_object(v___x_2179_);
                            v___x_2220_ = lean_box(0);
                            v___x_2221_ = lean_box(0);
                            v___x_2222_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(
                                    v___x_1845_,
                                    v___x_2208_,
                                    v_tk_2207_,
                                    v___x_2185_,
                                    v___y_2171_,
                                    v___y_2172_,
                                    v_val_2177_,
                                    v___x_1852_,
                                    v___x_2220_,
                                    v___x_2221_,
                                    v___y_2170_,
                                    v___y_2169_,
                                );
                            lean_dec(v_val_2177_);
                            lean_dec(v___x_2185_);
                            lean_dec(v_tk_2207_);
                            v___y_2160_ = v_opts_x3f_2175_;
                            v___y_2161_ = v___y_2170_;
                            v___y_2162_ = v___y_2172_;
                            v___y_2163_ = v___y_2173_;
                            v___y_2164_ = v___x_2176_;
                            v___y_2165_ = v___x_2222_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            13 => {
                v___x_2218_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___lam__0(
                    v___x_1845_,
                    v___x_2208_,
                    v_tk_2207_,
                    v___x_2185_,
                    v___y_2171_,
                    v___y_2172_,
                    v_val_2177_,
                    v___x_1852_,
                    v___x_2215_,
                    v___x_2217_,
                    v___y_2170_,
                    v___y_2169_,
                );
                lean_dec(v_val_2177_);
                lean_dec(v___x_2185_);
                lean_dec(v_tk_2207_);
                v___y_2160_ = v_opts_x3f_2175_;
                v___y_2161_ = v___y_2170_;
                v___y_2162_ = v___y_2172_;
                v___y_2163_ = v___y_2173_;
                v___y_2164_ = v___x_2176_;
                v___y_2165_ = v___x_2218_;
                state = 10;
                continue;
            }
            14 => {
                v___x_2230_ = lean_unsigned_to_nat(3);
                v___x_2231_ = l_Lean_Syntax_getArg(v_stx_1718_, v___x_2230_);
                v___x_2232_ = l_Lean_Syntax_isNone(v___x_2231_);
                if v___x_2232_ == 0 {
                    lean_inc(v___x_2231_);
                    v___x_2233_ = l_Lean_Syntax_matchesNull(v___x_2231_, v___x_1852_);
                    if v___x_2233_ == 0 {
                        lean_dec(v___x_2231_);
                        lean_dec(v_src_x3f_2229_);
                        lean_dec(v___y_2228_);
                        lean_dec(v___x_1851_);
                        lean_dec(v_doc_x3f_1719_);
                        v___x_2234_ =
                            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19;
                        v___x_2235_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_stx_1718_,
                            v___x_2234_,
                            v___y_2225_,
                            v___y_2226_,
                        );
                        lean_dec(v_stx_1718_);
                        return v___x_2235_;
                    } else {
                        v___x_2236_ = l_Lean_Syntax_getArg(v___x_2231_, v___x_1850_);
                        lean_dec(v___x_2231_);
                        v___x_2237_ =
                            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__120;
                        lean_inc(v___x_2236_);
                        v___x_2238_ = l_Lean_Syntax_isOfKind(v___x_2236_, v___x_2237_);
                        if v___x_2238_ == 0 {
                            lean_dec(v___x_2236_);
                            lean_dec(v_src_x3f_2229_);
                            lean_dec(v___y_2228_);
                            lean_dec(v___x_1851_);
                            lean_dec(v_doc_x3f_1719_);
                            v___x_2239_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19;
                            v___x_2240_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_stx_1718_,
                                v___x_2239_,
                                v___y_2225_,
                                v___y_2226_,
                            );
                            lean_dec(v_stx_1718_);
                            return v___x_2240_;
                        } else {
                            lean_dec(v_stx_1718_);
                            v_opts_x3f_2241_ = l_Lean_Syntax_getArg(v___x_2236_, v___x_1852_);
                            lean_dec(v___x_2236_);
                            v___x_2242_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2242_, 0, v_opts_x3f_2241_);
                            v___y_2169_ = v___y_2226_;
                            v___y_2170_ = v___y_2225_;
                            v___y_2171_ = v___x_2230_;
                            v___y_2172_ = v___y_2227_;
                            v___y_2173_ = v___y_2228_;
                            v___y_2174_ = v_src_x3f_2229_;
                            v_opts_x3f_2175_ = v___x_2242_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2231_);
                    lean_dec(v_stx_1718_);
                    v___x_2243_ = lean_box(0);
                    v___y_2169_ = v___y_2226_;
                    v___y_2170_ = v___y_2225_;
                    v___y_2171_ = v___x_2230_;
                    v___y_2172_ = v___y_2227_;
                    v___y_2173_ = v___y_2228_;
                    v___y_2174_ = v_src_x3f_2229_;
                    v_opts_x3f_2175_ = v___x_2243_;
                    state = 11;
                    continue;
                }
            }
            15 => {
                v___x_2248_ = lean_unsigned_to_nat(2);
                v___x_2249_ = l_Lean_Syntax_getArg(v_stx_1718_, v___x_2248_);
                v___x_2250_ = l_Lean_Syntax_isNone(v___x_2249_);
                if v___x_2250_ == 0 {
                    lean_inc(v___x_2249_);
                    v___x_2251_ = l_Lean_Syntax_matchesNull(v___x_2249_, v___x_1852_);
                    if v___x_2251_ == 0 {
                        lean_dec(v___x_2249_);
                        lean_dec(v_ver_x3f_2245_);
                        lean_dec(v___x_1851_);
                        lean_dec(v_doc_x3f_1719_);
                        v___x_2252_ =
                            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19;
                        v___x_2253_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_stx_1718_,
                            v___x_2252_,
                            v___y_2246_,
                            v___y_2247_,
                        );
                        lean_dec(v_stx_1718_);
                        return v___x_2253_;
                    } else {
                        v___x_2254_ = l_Lean_Syntax_getArg(v___x_2249_, v___x_1850_);
                        lean_dec(v___x_2249_);
                        v___x_2255_ =
                            l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__122;
                        lean_inc(v___x_2254_);
                        v___x_2256_ = l_Lean_Syntax_isOfKind(v___x_2254_, v___x_2255_);
                        if v___x_2256_ == 0 {
                            lean_dec(v___x_2254_);
                            lean_dec(v_ver_x3f_2245_);
                            lean_dec(v___x_1851_);
                            lean_dec(v_doc_x3f_1719_);
                            v___x_2257_ =
                                l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___closed__19;
                            v___x_2258_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_stx_1718_,
                                v___x_2257_,
                                v___y_2246_,
                                v___y_2247_,
                            );
                            lean_dec(v_stx_1718_);
                            return v___x_2258_;
                        } else {
                            v_src_x3f_2259_ = l_Lean_Syntax_getArg(v___x_2254_, v___x_1852_);
                            lean_dec(v___x_2254_);
                            v___x_2260_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2260_, 0, v_src_x3f_2259_);
                            v___y_2225_ = v___y_2246_;
                            v___y_2226_ = v___y_2247_;
                            v___y_2227_ = v___x_2248_;
                            v___y_2228_ = v_ver_x3f_2245_;
                            v_src_x3f_2229_ = v___x_2260_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2249_);
                    v___x_2261_ = lean_box(0);
                    v___y_2225_ = v___y_2246_;
                    v___y_2226_ = v___y_2247_;
                    v___y_2227_ = v___x_2248_;
                    v___y_2228_ = v_ver_x3f_2245_;
                    v_src_x3f_2229_ = v___x_2261_;
                    state = 14;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec___boxed(
    mut v_stx_2275_: *mut LeanObject,
    mut v_doc_x3f_2276_: *mut LeanObject,
    mut v_a_2277_: *mut LeanObject,
    mut v_a_2278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2279_: *mut LeanObject = core::ptr::null_mut();
    v_res_2279_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(
        v_stx_2275_,
        v_doc_x3f_2276_,
        v_a_2277_,
        v_a_2278_,
    );
    lean_dec_ref(v_a_2277_);
    return v_res_2279_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl(
    mut v_stx_2286_: *mut LeanObject,
    mut v_a_2287_: *mut LeanObject,
    mut v_a_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kw_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_spec_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2318_: u8 = 0;
    let mut v_a_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2327_: u8 = 0;
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2333_: u8 = 0;
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2289_ =
                    l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1;
                lean_inc(v_stx_2286_);
                v___x_2290_ = l_Lean_Syntax_isOfKind(v_stx_2286_, v___x_2289_);
                if v___x_2290_ == 0 {
                    v___x_2291_ =
                        l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__2;
                    v___x_2292_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_stx_2286_,
                        v___x_2291_,
                        v_a_2287_,
                        v_a_2288_,
                    );
                    lean_dec(v_stx_2286_);
                    return v___x_2292_;
                } else {
                    v___x_2293_ = lean_unsigned_to_nat(0);
                    v___x_2294_ = l_Lean_Syntax_getArg(v_stx_2286_, v___x_2293_);
                    v___x_2295_ = lean_unsigned_to_nat(1);
                    v_kw_2296_ = l_Lean_Syntax_getArg(v_stx_2286_, v___x_2295_);
                    v___x_2297_ = lean_unsigned_to_nat(2);
                    v_spec_2298_ = l_Lean_Syntax_getArg(v_stx_2286_, v___x_2297_);
                    lean_dec(v_stx_2286_);
                    v___x_2328_ = l_Lean_Syntax_getOptional_x3f(v___x_2294_);
                    lean_dec(v___x_2294_);
                    if lean_obj_tag(v___x_2328_) == 0 {
                        v___x_2329_ = lean_box(0);
                        v___y_2300_ = v___x_2329_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2330_ = lean_ctor_get(v___x_2328_, 0);
                        v_isSharedCheck_2337_ = (!lean_is_exclusive(v___x_2328_)) as u8;
                        if v_isSharedCheck_2337_ == 0 {
                            v___x_2332_ = v___x_2328_;
                            v_isShared_2333_ = v_isSharedCheck_2337_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_val_2330_);
                            lean_dec(v___x_2328_);
                            v___x_2332_ = lean_box(0);
                            v_isShared_2333_ = v_isSharedCheck_2337_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_methods_2301_ = lean_ctor_get(v_a_2287_, 0);
                v_quotContext_2302_ = lean_ctor_get(v_a_2287_, 1);
                v_currMacroScope_2303_ = lean_ctor_get(v_a_2287_, 2);
                v_currRecDepth_2304_ = lean_ctor_get(v_a_2287_, 3);
                v_maxRecDepth_2305_ = lean_ctor_get(v_a_2287_, 4);
                v_ref_2306_ = lean_ctor_get(v_a_2287_, 5);
                v_ref_2307_ = l_Lean_replaceRef(v_kw_2296_, v_ref_2306_);
                lean_dec(v_kw_2296_);
                lean_inc(v_maxRecDepth_2305_);
                lean_inc(v_currRecDepth_2304_);
                lean_inc(v_currMacroScope_2303_);
                lean_inc(v_quotContext_2302_);
                lean_inc(v_methods_2301_);
                v___x_2308_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_2308_, 0, v_methods_2301_);
                lean_ctor_set(v___x_2308_, 1, v_quotContext_2302_);
                lean_ctor_set(v___x_2308_, 2, v_currMacroScope_2303_);
                lean_ctor_set(v___x_2308_, 3, v_currRecDepth_2304_);
                lean_ctor_set(v___x_2308_, 4, v_maxRecDepth_2305_);
                lean_ctor_set(v___x_2308_, 5, v_ref_2307_);
                v___x_2309_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandDepSpec(
                    v_spec_2298_,
                    v___y_2300_,
                    v___x_2308_,
                    v_a_2288_,
                );
                lean_dec_ref_known(v___x_2308_, 6);
                if lean_obj_tag(v___x_2309_) == 0 {
                    v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
                    v_a_2311_ = lean_ctor_get(v___x_2309_, 1);
                    v_isSharedCheck_2318_ = (!lean_is_exclusive(v___x_2309_)) as u8;
                    if v_isSharedCheck_2318_ == 0 {
                        v___x_2313_ = v___x_2309_;
                        v_isShared_2314_ = v_isSharedCheck_2318_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2311_);
                        lean_inc(v_a_2310_);
                        lean_dec(v___x_2309_);
                        v___x_2313_ = lean_box(0);
                        v_isShared_2314_ = v_isSharedCheck_2318_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2319_ = lean_ctor_get(v___x_2309_, 0);
                    v_a_2320_ = lean_ctor_get(v___x_2309_, 1);
                    v_isSharedCheck_2327_ = (!lean_is_exclusive(v___x_2309_)) as u8;
                    if v_isSharedCheck_2327_ == 0 {
                        v___x_2322_ = v___x_2309_;
                        v_isShared_2323_ = v_isSharedCheck_2327_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2320_);
                        lean_inc(v_a_2319_);
                        lean_dec(v___x_2309_);
                        v___x_2322_ = lean_box(0);
                        v_isShared_2323_ = v_isSharedCheck_2327_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2314_ == 0 {
                    v___x_2316_ = v___x_2313_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2310_);
                    lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_a_2311_);
                    v___x_2316_ = v_reuseFailAlloc_2317_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2316_;
            }
            4 => {
                if v_isShared_2323_ == 0 {
                    v___x_2325_ = v___x_2322_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2319_);
                    lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_a_2320_);
                    v___x_2325_ = v_reuseFailAlloc_2326_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2325_;
            }
            6 => {
                if v_isShared_2333_ == 0 {
                    v___x_2335_ = v___x_2332_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_val_2330_);
                    v___x_2335_ = v_reuseFailAlloc_2336_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2300_ = v___x_2335_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___boxed(
    mut v_stx_2338_: *mut LeanObject,
    mut v_a_2339_: *mut LeanObject,
    mut v_a_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2341_: *mut LeanObject = core::ptr::null_mut();
    v_res_2341_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl(
        v_stx_2338_,
        v_a_2339_,
        v_a_2340_,
    );
    lean_dec_ref(v_a_2339_);
    return v_res_2341_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1()
-> *mut LeanObject {
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    v___x_2370_ = l_Lean_Elab_macroAttribute;
    v___x_2371_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___closed__1;
    v___x_2372_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___closed__10;
    v___x_2373_ = lean_alloc_closure(
        l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___boxed
            as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_2374_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2370_,
        v___x_2371_,
        v___x_2372_,
        v___x_2373_,
    );
    return v___x_2374_;
}
pub unsafe fn l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1___boxed(
    mut v_a_2375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2376_: *mut LeanObject = core::ptr::null_mut();
    v_res_2376_ = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1();
    return v_res_2376_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Require(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dependency(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl___regBuiltin___private_Lake_DSL_Require_0__Lake_DSL_expandRequireDecl__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Require(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Require(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_DSL_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Dependency(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Require(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Require(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_DSL_Require(builtin);
}

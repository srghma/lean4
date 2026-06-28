// Lean compiler output
// Module: Lake.DSL.Script
// Imports: Init.Prelude Lake.Config.Package Lake.DSL.Attributes Lake.DSL.Syntax
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_SepArray_ofElems, l_Lean_Syntax_isNone};
use crate::r#gen::Init::Prelude::{
    initialize_Init_Prelude, l_Array_mkArray0, l_Array_mkArray1___redArg,
    l_Lean_Macro_throwErrorAt___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node7, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27, runtime_initialize_Init_Prelude,
};
use crate::r#gen::Lake::Config::Package::{
    initialize_Lake_Config_Package, runtime_initialize_Lake_Config_Package,
};
use crate::r#gen::Lake::DSL::Attributes::{
    initialize_Lake_DSL_Attributes, runtime_initialize_Lake_DSL_Attributes,
};
use crate::r#gen::Lake::DSL::DeclUtil::{
    l_Lake_DSL_expandAttrs, l_Lake_DSL_expandIdentOrStrAsIdent, l_Lake_DSL_expandOptSimpleBinder,
};
use crate::r#gen::Lake::DSL::Syntax::{
    initialize_Lake_DSL_Syntax, runtime_initialize_Lake_DSL_Syntax,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value:
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
    m_data: [115, 99, 114, 105, 112, 116, 68, 101, 99, 108, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_0:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_1:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value
        ) as *mut LeanObject,
        11447824861308129923 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4_value:
    LeanStringObject<30> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 115, 99, 114, 105, 112, 116, 32, 100,
        101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value:
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
    m_data: [83, 99, 114, 105, 112, 116, 70, 110, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value
        ) as *mut LeanObject,
        10003671174329666725 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value_aux_0:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value
        ) as *mut LeanObject,
        16942896190233842921 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22_value:
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
    m_data: [102, 117, 110, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23_value:
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
    m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24_value:
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
    m_data: [61, 62, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 8,
    m_data: [194, 171, 115, 99, 114, 105, 112, 116, 194, 187, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34_value)
        as *mut LeanObject;
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36_value:
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
    m_data: [115, 99, 114, 105, 112, 116, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36_value
        ) as *mut LeanObject,
        887671011676595348 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44_value:
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
    m_data: [100, 101, 99, 108, 86, 97, 108, 68, 111, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_0:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_1:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44_value
        ) as *mut LeanObject,
        11022427548561232637 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_0:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_1:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_2:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40_value
        ) as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41_value
        ) as *mut LeanObject,
        13585030837571646948 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_0:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_1:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_2:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42_value
        ) as *mut LeanObject,
        7625897890118033792 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43_value
        ) as *mut LeanObject,
        8715860392475343861 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50_value:
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
    m_data: [119, 104, 101, 114, 101, 68, 101, 99, 108, 115, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_0:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_1:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_2:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50_value
        ) as *mut LeanObject,
        4503069825835506739 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52_value:
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
    m_data: [100, 111, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_0:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_1:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_2:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52_value
        ) as *mut LeanObject,
        5817315006727311029 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54_value:
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
        115, 99, 114, 105, 112, 116, 68, 101, 99, 108, 83, 112, 101, 99, 0,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54_value)
        as *mut LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_0:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_1:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value
        ) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value:
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
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54_value
        ) as *mut LeanObject,
        7959617833543045482 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value)
        as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value) as *mut LeanObject,12997130533650095963 as *mut LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value) as *mut LeanObject,11286550318989764116 as *mut LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 99, 114, 105, 112, 116, 0]};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4_value) as *mut LeanObject,6321669005470951828 as *mut LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,1573984873544968597 as *mut LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value) as *mut LeanObject,15189868043128492961 as *mut LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value) as *mut LeanObject,1611460809877233174 as *mut LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 120, 112, 97, 110, 100, 83, 99, 114, 105, 112, 116, 68, 101, 99, 108, 0]};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9_value) as *mut LeanObject,11098910053431617253 as *mut LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10_value) as *mut LeanObject;
pub unsafe fn _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17()
-> *mut LeanObject {
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    v___x_578_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16;
    v___x_579_ = l_String_toRawSubstring_x27(v___x_578_);
    return v___x_579_;
}
pub unsafe fn _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31()
-> *mut LeanObject {
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Array_mkArray0(lean_box(0));
    return v___x_600_;
}
pub unsafe fn _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35()
-> *mut LeanObject {
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    v___x_604_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34;
    v___x_605_ = l_String_toRawSubstring_x27(v___x_604_);
    return v___x_605_;
}
pub unsafe fn l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl(
    mut v_x_649_: *mut LeanObject,
    mut v_a_650_: *mut LeanObject,
    mut v_a_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u8 = 0;
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_790_: u8 = 0;
    let mut v___y_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_850_: u8 = 0;
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_854_: u8 = 0;
    let mut v___y_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: u8 = 0;
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_x3f_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: u8 = 0;
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u8 = 0;
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: u8 = 0;
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: u8 = 0;
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: u8 = 0;
    let mut v___x_998_: u8 = 0;
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: u8 = 0;
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: u8 = 0;
    let mut v___x_1019_: u8 = 0;
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: u8 = 0;
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: u8 = 0;
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kw_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: u8 = 0;
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_x3f_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: u8 = 0;
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_675_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3;
                lean_inc(v_x_649_);
                v___x_698_ = l_Lean_Syntax_isOfKind(v_x_649_, v___x_675_);
                if v___x_698_ == 0 {
                    v___x_699_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                    v___x_700_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_x_649_, v___x_699_, v_a_650_, v_a_651_,
                    );
                    lean_dec(v_x_649_);
                    return v___x_700_;
                } else {
                    v___x_701_ = lean_unsigned_to_nat(0);
                    v___x_1065_ = l_Lean_Syntax_getArg(v_x_649_, v___x_701_);
                    v___x_1066_ = l_Lean_Syntax_isNone(v___x_1065_);
                    if v___x_1066_ == 0 {
                        v___x_1067_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_1065_);
                        v___x_1068_ = l_Lean_Syntax_matchesNull(v___x_1065_, v___x_1067_);
                        if v___x_1068_ == 0 {
                            lean_dec(v___x_1065_);
                            v___x_1069_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                            v___x_1070_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_x_649_,
                                v___x_1069_,
                                v_a_650_,
                                v_a_651_,
                            );
                            lean_dec(v_x_649_);
                            return v___x_1070_;
                        } else {
                            v_doc_x3f_1071_ = l_Lean_Syntax_getArg(v___x_1065_, v___x_701_);
                            lean_dec(v___x_1065_);
                            v___x_1072_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1072_, 0, v_doc_x3f_1071_);
                            v_doc_x3f_1053_ = v___x_1072_;
                            v___y_1054_ = v_a_650_;
                            v___y_1055_ = v_a_651_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1065_);
                        v___x_1073_ = lean_box(0);
                        v_doc_x3f_1053_ = v___x_1073_;
                        v___y_1054_ = v_a_650_;
                        v___y_1055_ = v_a_651_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_666_);
                v___x_669_ = l_Array_append___redArg(v___y_666_, v___y_668_);
                lean_dec_ref(v___y_668_);
                lean_inc(v___y_667_);
                lean_inc_n(v___y_663_, 3);
                v___x_670_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_670_, 0, v___y_663_);
                lean_ctor_set(v___x_670_, 1, v___y_667_);
                lean_ctor_set(v___x_670_, 2, v___x_669_);
                lean_inc(v___y_664_);
                v___x_671_ = l_Lean_Syntax_node4(
                    v___y_663_, v___y_664_, v___y_661_, v___y_662_, v___y_665_, v___x_670_,
                );
                v___x_672_ = l_Lean_Syntax_node5(
                    v___y_663_, v___y_654_, v___y_656_, v___y_659_, v___y_653_, v___x_671_,
                    v___y_657_,
                );
                v___x_673_ = l_Lean_Syntax_node2(v___y_663_, v___y_660_, v___y_658_, v___x_672_);
                v___x_674_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_674_, 0, v___x_673_);
                lean_ctor_set(v___x_674_, 1, v___y_655_);
                return v___x_674_;
            }
            2 => {
                lean_inc_ref(v___y_682_);
                v___x_692_ = l_Array_append___redArg(v___y_682_, v___y_691_);
                lean_dec_ref(v___y_691_);
                lean_inc(v___y_683_);
                lean_inc_n(v___y_678_, 3);
                v___x_693_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_693_, 0, v___y_678_);
                lean_ctor_set(v___x_693_, 1, v___y_683_);
                lean_ctor_set(v___x_693_, 2, v___x_692_);
                v___x_694_ = l_Lean_Syntax_node4(
                    v___y_678_, v___y_689_, v___y_687_, v___y_681_, v___y_677_, v___x_693_,
                );
                lean_inc(v___y_679_);
                v___x_695_ =
                    l_Lean_Syntax_node3(v___y_678_, v___y_679_, v___y_686_, v___y_688_, v___x_694_);
                v___x_696_ = l_Lean_Syntax_node4(
                    v___y_678_, v___x_675_, v___y_690_, v___y_685_, v___y_680_, v___x_695_,
                );
                v___x_697_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_697_, 0, v___x_696_);
                lean_ctor_set(v___x_697_, 1, v___y_684_);
                return v___x_697_;
            }
            3 => {
                lean_inc_ref_n(v___y_722_, 2);
                v___x_726_ = l_Array_append___redArg(v___y_722_, v___y_725_);
                lean_dec_ref(v___y_725_);
                lean_inc_n(v___y_723_, 6);
                lean_inc_n(v___y_720_, 20);
                v___x_727_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_727_, 0, v___y_720_);
                lean_ctor_set(v___x_727_, 1, v___y_723_);
                lean_ctor_set(v___x_727_, 2, v___x_726_);
                v___x_728_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5;
                lean_inc_ref_n(v___y_717_, 3);
                lean_inc_ref_n(v___y_715_, 7);
                lean_inc_ref_n(v___y_714_, 7);
                v___x_729_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_717_, v___x_728_);
                v___x_730_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6;
                v___x_731_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_731_, 0, v___y_720_);
                lean_ctor_set(v___x_731_, 1, v___x_730_);
                v___x_732_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7;
                v___x_733_ = l_Lean_Syntax_SepArray_ofElems(v___x_732_, v___y_713_);
                lean_dec_ref(v___y_713_);
                v___x_734_ = l_Array_append___redArg(v___y_722_, v___x_733_);
                lean_dec_ref(v___x_733_);
                v___x_735_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_735_, 0, v___y_720_);
                lean_ctor_set(v___x_735_, 1, v___y_723_);
                lean_ctor_set(v___x_735_, 2, v___x_734_);
                v___x_736_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8;
                v___x_737_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_737_, 0, v___y_720_);
                lean_ctor_set(v___x_737_, 1, v___x_736_);
                v___x_738_ =
                    l_Lean_Syntax_node3(v___y_720_, v___x_729_, v___x_731_, v___x_735_, v___x_737_);
                v___x_739_ = l_Lean_Syntax_node1(v___y_720_, v___y_723_, v___x_738_);
                lean_inc_n(v___y_708_, 9);
                v___x_740_ = l_Lean_Syntax_node7(
                    v___y_720_, v___y_710_, v___x_727_, v___x_739_, v___y_708_, v___y_708_,
                    v___y_708_, v___y_708_, v___y_708_,
                );
                v___x_741_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9;
                lean_inc_ref_n(v___y_712_, 3);
                v___x_742_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_712_, v___x_741_);
                v___x_743_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10;
                v___x_744_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_744_, 0, v___y_720_);
                lean_ctor_set(v___x_744_, 1, v___x_743_);
                v___x_745_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11;
                v___x_746_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_712_, v___x_745_);
                v___x_747_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12;
                v___x_748_ = lean_box(2);
                v___x_749_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_749_, 0, v___x_748_);
                lean_ctor_set(v___x_749_, 1, v___y_723_);
                lean_ctor_set(v___x_749_, 2, v___x_747_);
                v___x_750_ = lean_mk_empty_array_with_capacity(v___y_719_);
                v___x_751_ = lean_array_push(v___x_750_, v___y_716_);
                v___x_752_ = lean_array_push(v___x_751_, v___x_749_);
                v___x_753_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_753_, 0, v___x_748_);
                lean_ctor_set(v___x_753_, 1, v___x_746_);
                lean_ctor_set(v___x_753_, 2, v___x_752_);
                v___x_754_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13;
                v___x_755_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_712_, v___x_754_);
                v___x_756_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14;
                v___x_757_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_717_, v___x_756_);
                v___x_758_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15;
                v___x_759_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_759_, 0, v___y_720_);
                lean_ctor_set(v___x_759_, 1, v___x_758_);
                v___x_760_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17_once
                    ),
                    _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17,
                );
                v___x_761_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18;
                v___x_762_ = l_Lean_addMacroScope(v___y_705_, v___x_761_, v___y_704_);
                v___x_763_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20;
                lean_inc(v___y_724_);
                v___x_764_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_764_, 0, v___x_763_);
                lean_ctor_set(v___x_764_, 1, v___y_724_);
                v___x_765_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_765_, 0, v___y_720_);
                lean_ctor_set(v___x_765_, 1, v___x_760_);
                lean_ctor_set(v___x_765_, 2, v___x_762_);
                lean_ctor_set(v___x_765_, 3, v___x_764_);
                v___x_766_ = l_Lean_Syntax_node2(v___y_720_, v___x_757_, v___x_759_, v___x_765_);
                v___x_767_ = l_Lean_Syntax_node1(v___y_720_, v___y_723_, v___x_766_);
                v___x_768_ = l_Lean_Syntax_node2(v___y_720_, v___x_755_, v___y_708_, v___x_767_);
                v___x_769_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21;
                v___x_770_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_770_, 0, v___y_720_);
                lean_ctor_set(v___x_770_, 1, v___x_769_);
                v___x_771_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22;
                v___x_772_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_717_, v___x_771_);
                v___x_773_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_773_, 0, v___y_720_);
                lean_ctor_set(v___x_773_, 1, v___x_771_);
                v___x_774_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23;
                v___x_775_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_717_, v___x_774_);
                v___x_776_ = l_Lean_Syntax_node1(v___y_720_, v___y_723_, v___y_718_);
                v___x_777_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24;
                v___x_778_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_778_, 0, v___y_720_);
                lean_ctor_set(v___x_778_, 1, v___x_777_);
                v___x_779_ = l_Lean_Syntax_node4(
                    v___y_720_, v___x_775_, v___x_776_, v___y_708_, v___x_778_, v___y_707_,
                );
                v___x_780_ = l_Lean_Syntax_node2(v___y_720_, v___x_772_, v___x_773_, v___x_779_);
                lean_inc(v___y_709_);
                v___x_781_ = l_Lean_Syntax_node2(v___y_720_, v___y_709_, v___y_708_, v___y_708_);
                if lean_obj_tag(v___y_703_) == 1 {
                    v_val_782_ = lean_ctor_get(v___y_703_, 0);
                    lean_inc(v_val_782_);
                    lean_dec_ref_known(v___y_703_, 1);
                    v___x_783_ = l_Array_mkArray1___redArg(v_val_782_);
                    v___y_653_ = v___x_768_;
                    v___y_654_ = v___x_742_;
                    v___y_655_ = v___y_706_;
                    v___y_656_ = v___x_744_;
                    v___y_657_ = v___y_708_;
                    v___y_658_ = v___x_740_;
                    v___y_659_ = v___x_753_;
                    v___y_660_ = v___y_711_;
                    v___y_661_ = v___x_770_;
                    v___y_662_ = v___x_780_;
                    v___y_663_ = v___y_720_;
                    v___y_664_ = v___y_721_;
                    v___y_665_ = v___x_781_;
                    v___y_666_ = v___y_722_;
                    v___y_667_ = v___y_723_;
                    v___y_668_ = v___x_783_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_703_);
                    v___x_784_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
                    v___y_653_ = v___x_768_;
                    v___y_654_ = v___x_742_;
                    v___y_655_ = v___y_706_;
                    v___y_656_ = v___x_744_;
                    v___y_657_ = v___y_708_;
                    v___y_658_ = v___x_740_;
                    v___y_659_ = v___x_753_;
                    v___y_660_ = v___y_711_;
                    v___y_661_ = v___x_770_;
                    v___y_662_ = v___x_780_;
                    v___y_663_ = v___y_720_;
                    v___y_664_ = v___y_721_;
                    v___y_665_ = v___x_781_;
                    v___y_666_ = v___y_722_;
                    v___y_667_ = v___y_723_;
                    v___y_668_ = v___x_784_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v_methods_803_ = lean_ctor_get(v___y_801_, 0);
                v_quotContext_804_ = lean_ctor_get(v___y_801_, 1);
                v_currMacroScope_805_ = lean_ctor_get(v___y_801_, 2);
                v_currRecDepth_806_ = lean_ctor_get(v___y_801_, 3);
                v_maxRecDepth_807_ = lean_ctor_get(v___y_801_, 4);
                v_ref_808_ = lean_ctor_get(v___y_801_, 5);
                v_ref_809_ = l_Lean_replaceRef(v___y_786_, v_ref_808_);
                lean_dec(v___y_786_);
                lean_inc(v_ref_809_);
                lean_inc(v_maxRecDepth_807_);
                lean_inc(v_currRecDepth_806_);
                lean_inc(v_currMacroScope_805_);
                lean_inc(v_quotContext_804_);
                lean_inc(v_methods_803_);
                v___x_810_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_810_, 0, v_methods_803_);
                lean_ctor_set(v___x_810_, 1, v_quotContext_804_);
                lean_ctor_set(v___x_810_, 2, v_currMacroScope_805_);
                lean_ctor_set(v___x_810_, 3, v_currRecDepth_806_);
                lean_ctor_set(v___x_810_, 4, v_maxRecDepth_807_);
                lean_ctor_set(v___x_810_, 5, v_ref_809_);
                v___x_811_ = l_Lake_DSL_expandOptSimpleBinder(v___y_787_, v___x_810_, v___y_802_);
                lean_dec_ref_known(v___x_810_, 6);
                if lean_obj_tag(v___x_811_) == 0 {
                    v_a_812_ = lean_ctor_get(v___x_811_, 0);
                    lean_inc(v_a_812_);
                    v_a_813_ = lean_ctor_get(v___x_811_, 1);
                    lean_inc(v_a_813_);
                    lean_dec_ref_known(v___x_811_, 2);
                    v_id_814_ = l_Lake_DSL_expandIdentOrStrAsIdent(v___y_794_);
                    v___x_815_ = l_Lean_SourceInfo_fromRef(v_ref_809_, v___y_790_);
                    lean_dec(v_ref_809_);
                    v___x_816_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26;
                    v___x_817_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27;
                    lean_inc_ref_n(v___y_796_, 5);
                    lean_inc_ref_n(v___y_795_, 5);
                    v___x_818_ = l_Lean_Name_mkStr4(v___y_795_, v___y_796_, v___x_816_, v___x_817_);
                    v___x_819_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28;
                    v___x_820_ = l_Lean_Name_mkStr4(v___y_795_, v___y_796_, v___x_816_, v___x_819_);
                    v___x_821_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30;
                    v___x_822_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31), core::ptr::addr_of_mut!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once), _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31);
                    lean_inc_n(v___x_815_, 5);
                    v___x_823_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_823_, 0, v___x_815_);
                    lean_ctor_set(v___x_823_, 1, v___x_821_);
                    lean_ctor_set(v___x_823_, 2, v___x_822_);
                    lean_inc_ref_n(v___x_823_, 2);
                    v___x_824_ = l_Lean_Syntax_node1(v___x_815_, v___x_820_, v___x_823_);
                    v___x_825_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32;
                    v___x_826_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33;
                    v___x_827_ = l_Lean_Name_mkStr4(v___y_795_, v___y_796_, v___x_825_, v___x_826_);
                    v___x_828_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35), core::ptr::addr_of_mut!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35_once), _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35);
                    v___x_829_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37;
                    lean_inc(v_currMacroScope_805_);
                    lean_inc(v_quotContext_804_);
                    v___x_830_ =
                        l_Lean_addMacroScope(v_quotContext_804_, v___x_829_, v_currMacroScope_805_);
                    v___x_831_ = lean_box(0);
                    v___x_832_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_832_, 0, v___x_815_);
                    lean_ctor_set(v___x_832_, 1, v___x_828_);
                    lean_ctor_set(v___x_832_, 2, v___x_830_);
                    lean_ctor_set(v___x_832_, 3, v___x_831_);
                    v___x_833_ =
                        l_Lean_Syntax_node2(v___x_815_, v___x_827_, v___x_832_, v___x_823_);
                    v___x_834_ =
                        l_Lean_Syntax_node2(v___x_815_, v___x_818_, v___x_824_, v___x_833_);
                    v___x_835_ = lean_mk_empty_array_with_capacity(v___y_789_);
                    v___x_836_ = lean_array_push(v___x_835_, v___x_834_);
                    v___x_837_ = l_Lake_DSL_expandAttrs(v___y_791_);
                    v___x_838_ = l_Array_append___redArg(v___x_836_, v___x_837_);
                    lean_dec_ref(v___x_837_);
                    v___x_839_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38;
                    lean_inc_ref_n(v___y_793_, 2);
                    v___x_840_ = l_Lean_Name_mkStr4(v___y_795_, v___y_796_, v___y_793_, v___x_839_);
                    v___x_841_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39;
                    v___x_842_ = l_Lean_Name_mkStr4(v___y_795_, v___y_796_, v___y_793_, v___x_841_);
                    if lean_obj_tag(v___y_799_) == 1 {
                        v_val_843_ = lean_ctor_get(v___y_799_, 0);
                        lean_inc(v_val_843_);
                        lean_dec_ref_known(v___y_799_, 1);
                        v___x_844_ = l_Array_mkArray1___redArg(v_val_843_);
                        lean_inc(v_quotContext_804_);
                        lean_inc(v_currMacroScope_805_);
                        v___y_703_ = v_wds_x3f_800_;
                        v___y_704_ = v_currMacroScope_805_;
                        v___y_705_ = v_quotContext_804_;
                        v___y_706_ = v_a_813_;
                        v___y_707_ = v___y_788_;
                        v___y_708_ = v___x_823_;
                        v___y_709_ = v___y_792_;
                        v___y_710_ = v___x_842_;
                        v___y_711_ = v___x_840_;
                        v___y_712_ = v___y_793_;
                        v___y_713_ = v___x_838_;
                        v___y_714_ = v___y_795_;
                        v___y_715_ = v___y_796_;
                        v___y_716_ = v_id_814_;
                        v___y_717_ = v___x_816_;
                        v___y_718_ = v_a_812_;
                        v___y_719_ = v___y_797_;
                        v___y_720_ = v___x_815_;
                        v___y_721_ = v___y_798_;
                        v___y_722_ = v___x_822_;
                        v___y_723_ = v___x_821_;
                        v___y_724_ = v___x_831_;
                        v___y_725_ = v___x_844_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___y_799_);
                        v___x_845_ =
                            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
                        lean_inc(v_quotContext_804_);
                        lean_inc(v_currMacroScope_805_);
                        v___y_703_ = v_wds_x3f_800_;
                        v___y_704_ = v_currMacroScope_805_;
                        v___y_705_ = v_quotContext_804_;
                        v___y_706_ = v_a_813_;
                        v___y_707_ = v___y_788_;
                        v___y_708_ = v___x_823_;
                        v___y_709_ = v___y_792_;
                        v___y_710_ = v___x_842_;
                        v___y_711_ = v___x_840_;
                        v___y_712_ = v___y_793_;
                        v___y_713_ = v___x_838_;
                        v___y_714_ = v___y_795_;
                        v___y_715_ = v___y_796_;
                        v___y_716_ = v_id_814_;
                        v___y_717_ = v___x_816_;
                        v___y_718_ = v_a_812_;
                        v___y_719_ = v___y_797_;
                        v___y_720_ = v___x_815_;
                        v___y_721_ = v___y_798_;
                        v___y_722_ = v___x_822_;
                        v___y_723_ = v___x_821_;
                        v___y_724_ = v___x_831_;
                        v___y_725_ = v___x_845_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_ref_809_);
                    lean_dec(v_wds_x3f_800_);
                    lean_dec(v___y_799_);
                    lean_dec(v___y_794_);
                    lean_dec(v___y_791_);
                    lean_dec(v___y_788_);
                    v_a_846_ = lean_ctor_get(v___x_811_, 0);
                    v_a_847_ = lean_ctor_get(v___x_811_, 1);
                    v_isSharedCheck_854_ = (!lean_is_exclusive(v___x_811_)) as u8;
                    if v_isSharedCheck_854_ == 0 {
                        v___x_849_ = v___x_811_;
                        v_isShared_850_ = v_isSharedCheck_854_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_847_);
                        lean_inc(v_a_846_);
                        lean_dec(v___x_811_);
                        v___x_849_ = lean_box(0);
                        v_isShared_850_ = v_isSharedCheck_854_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_850_ == 0 {
                    v___x_852_ = v___x_849_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_846_);
                    lean_ctor_set(v_reuseFailAlloc_853_, 1, v_a_847_);
                    v___x_852_ = v_reuseFailAlloc_853_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_852_;
            }
            7 => {
                lean_inc_ref_n(v___y_860_, 2);
                v___x_872_ = l_Array_append___redArg(v___y_860_, v___y_871_);
                lean_dec_ref(v___y_871_);
                lean_inc_n(v___y_861_, 2);
                lean_inc_n(v___y_856_, 6);
                v___x_873_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_873_, 0, v___y_856_);
                lean_ctor_set(v___x_873_, 1, v___y_861_);
                lean_ctor_set(v___x_873_, 2, v___x_872_);
                v___x_874_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40;
                v___x_875_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41;
                lean_inc_ref_n(v___y_859_, 2);
                lean_inc_ref_n(v___y_870_, 2);
                v___x_876_ = l_Lean_Name_mkStr4(v___y_870_, v___y_859_, v___x_874_, v___x_875_);
                v___x_877_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21;
                v___x_878_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_878_, 0, v___y_856_);
                lean_ctor_set(v___x_878_, 1, v___x_877_);
                lean_inc_ref(v___y_862_);
                v___x_879_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_879_, 0, v___y_856_);
                lean_ctor_set(v___x_879_, 1, v___y_862_);
                lean_inc(v___y_868_);
                v___x_880_ = l_Lean_Syntax_node2(v___y_856_, v___y_868_, v___x_879_, v___y_869_);
                v___x_881_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42;
                v___x_882_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43;
                v___x_883_ = l_Lean_Name_mkStr4(v___y_870_, v___y_859_, v___x_881_, v___x_882_);
                v___x_884_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_884_, 0, v___y_856_);
                lean_ctor_set(v___x_884_, 1, v___y_861_);
                lean_ctor_set(v___x_884_, 2, v___y_860_);
                lean_inc_ref(v___x_884_);
                v___x_885_ = l_Lean_Syntax_node2(v___y_856_, v___x_883_, v___x_884_, v___x_884_);
                if lean_obj_tag(v___y_864_) == 1 {
                    v_val_886_ = lean_ctor_get(v___y_864_, 0);
                    lean_inc(v_val_886_);
                    lean_dec_ref_known(v___y_864_, 1);
                    v___x_887_ = l_Array_mkArray1___redArg(v_val_886_);
                    v___y_677_ = v___x_885_;
                    v___y_678_ = v___y_856_;
                    v___y_679_ = v___y_857_;
                    v___y_680_ = v___y_858_;
                    v___y_681_ = v___x_880_;
                    v___y_682_ = v___y_860_;
                    v___y_683_ = v___y_861_;
                    v___y_684_ = v___y_863_;
                    v___y_685_ = v___y_865_;
                    v___y_686_ = v___y_866_;
                    v___y_687_ = v___x_878_;
                    v___y_688_ = v___x_873_;
                    v___y_689_ = v___x_876_;
                    v___y_690_ = v___y_867_;
                    v___y_691_ = v___x_887_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_864_);
                    v___x_888_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
                    v___y_677_ = v___x_885_;
                    v___y_678_ = v___y_856_;
                    v___y_679_ = v___y_857_;
                    v___y_680_ = v___y_858_;
                    v___y_681_ = v___x_880_;
                    v___y_682_ = v___y_860_;
                    v___y_683_ = v___y_861_;
                    v___y_684_ = v___y_863_;
                    v___y_685_ = v___y_865_;
                    v___y_686_ = v___y_866_;
                    v___y_687_ = v___x_878_;
                    v___y_688_ = v___x_873_;
                    v___y_689_ = v___x_876_;
                    v___y_690_ = v___y_867_;
                    v___y_691_ = v___x_888_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                lean_inc_ref(v___y_895_);
                v___x_906_ = l_Array_append___redArg(v___y_895_, v___y_905_);
                lean_dec_ref(v___y_905_);
                lean_inc(v___y_896_);
                lean_inc(v___y_892_);
                v___x_907_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_907_, 0, v___y_892_);
                lean_ctor_set(v___x_907_, 1, v___y_896_);
                lean_ctor_set(v___x_907_, 2, v___x_906_);
                v___x_908_ = l_Lean_SourceInfo_fromRef(v___y_891_, v___x_698_);
                lean_dec(v___y_891_);
                v___x_909_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36;
                v___x_910_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_910_, 0, v___x_908_);
                lean_ctor_set(v___x_910_, 1, v___x_909_);
                if lean_obj_tag(v___y_890_) == 1 {
                    v_val_911_ = lean_ctor_get(v___y_890_, 0);
                    lean_inc(v_val_911_);
                    lean_dec_ref_known(v___y_890_, 1);
                    v___x_912_ = l_Array_mkArray1___redArg(v_val_911_);
                    v___y_856_ = v___y_892_;
                    v___y_857_ = v___y_893_;
                    v___y_858_ = v___x_910_;
                    v___y_859_ = v___y_894_;
                    v___y_860_ = v___y_895_;
                    v___y_861_ = v___y_896_;
                    v___y_862_ = v___y_897_;
                    v___y_863_ = v___y_898_;
                    v___y_864_ = v___y_899_;
                    v___y_865_ = v___x_907_;
                    v___y_866_ = v___y_900_;
                    v___y_867_ = v___y_901_;
                    v___y_868_ = v___y_902_;
                    v___y_869_ = v___y_903_;
                    v___y_870_ = v___y_904_;
                    v___y_871_ = v___x_912_;
                    state = 7;
                    continue;
                } else {
                    lean_dec(v___y_890_);
                    v___x_913_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
                    v___y_856_ = v___y_892_;
                    v___y_857_ = v___y_893_;
                    v___y_858_ = v___x_910_;
                    v___y_859_ = v___y_894_;
                    v___y_860_ = v___y_895_;
                    v___y_861_ = v___y_896_;
                    v___y_862_ = v___y_897_;
                    v___y_863_ = v___y_898_;
                    v___y_864_ = v___y_899_;
                    v___y_865_ = v___x_907_;
                    v___y_866_ = v___y_900_;
                    v___y_867_ = v___y_901_;
                    v___y_868_ = v___y_902_;
                    v___y_869_ = v___y_903_;
                    v___y_870_ = v___y_904_;
                    v___y_871_ = v___x_913_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                lean_inc_ref(v___y_921_);
                v___x_931_ = l_Array_append___redArg(v___y_921_, v___y_930_);
                lean_dec_ref(v___y_930_);
                lean_inc(v___y_922_);
                lean_inc(v___y_917_);
                v___x_932_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_932_, 0, v___y_917_);
                lean_ctor_set(v___x_932_, 1, v___y_922_);
                lean_ctor_set(v___x_932_, 2, v___x_931_);
                if lean_obj_tag(v___y_919_) == 1 {
                    v_val_933_ = lean_ctor_get(v___y_919_, 0);
                    lean_inc(v_val_933_);
                    lean_dec_ref_known(v___y_919_, 1);
                    v___x_934_ = l_Array_mkArray1___redArg(v_val_933_);
                    v___y_890_ = v___y_915_;
                    v___y_891_ = v___y_916_;
                    v___y_892_ = v___y_917_;
                    v___y_893_ = v___y_918_;
                    v___y_894_ = v___y_920_;
                    v___y_895_ = v___y_921_;
                    v___y_896_ = v___y_922_;
                    v___y_897_ = v___y_923_;
                    v___y_898_ = v___y_924_;
                    v___y_899_ = v___y_925_;
                    v___y_900_ = v___y_926_;
                    v___y_901_ = v___x_932_;
                    v___y_902_ = v___y_927_;
                    v___y_903_ = v___y_928_;
                    v___y_904_ = v___y_929_;
                    v___y_905_ = v___x_934_;
                    state = 8;
                    continue;
                } else {
                    lean_dec(v___y_919_);
                    v___x_935_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
                    v___y_890_ = v___y_915_;
                    v___y_891_ = v___y_916_;
                    v___y_892_ = v___y_917_;
                    v___y_893_ = v___y_918_;
                    v___y_894_ = v___y_920_;
                    v___y_895_ = v___y_921_;
                    v___y_896_ = v___y_922_;
                    v___y_897_ = v___y_923_;
                    v___y_898_ = v___y_924_;
                    v___y_899_ = v___y_925_;
                    v___y_900_ = v___y_926_;
                    v___y_901_ = v___x_932_;
                    v___y_902_ = v___y_927_;
                    v___y_903_ = v___y_928_;
                    v___y_904_ = v___y_929_;
                    v___y_905_ = v___x_935_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v_ref_951_ = lean_ctor_get(v___y_949_, 5);
                v___x_952_ = 0;
                v___x_953_ = l_Lean_SourceInfo_fromRef(v_ref_951_, v___x_952_);
                v___x_954_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30;
                v___x_955_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once
                    ),
                    _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31,
                );
                if lean_obj_tag(v___y_945_) == 1 {
                    v_val_956_ = lean_ctor_get(v___y_945_, 0);
                    lean_inc(v_val_956_);
                    lean_dec_ref_known(v___y_945_, 1);
                    v___x_957_ = l_Array_mkArray1___redArg(v_val_956_);
                    v___y_915_ = v___y_939_;
                    v___y_916_ = v___y_938_;
                    v___y_917_ = v___x_953_;
                    v___y_918_ = v___y_941_;
                    v___y_919_ = v___y_943_;
                    v___y_920_ = v___y_942_;
                    v___y_921_ = v___x_955_;
                    v___y_922_ = v___x_954_;
                    v___y_923_ = v___y_937_;
                    v___y_924_ = v___y_950_;
                    v___y_925_ = v_wds_x3f_948_;
                    v___y_926_ = v___y_940_;
                    v___y_927_ = v___y_944_;
                    v___y_928_ = v___y_946_;
                    v___y_929_ = v___y_947_;
                    v___y_930_ = v___x_957_;
                    state = 9;
                    continue;
                } else {
                    lean_dec(v___y_945_);
                    v___x_958_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
                    v___y_915_ = v___y_939_;
                    v___y_916_ = v___y_938_;
                    v___y_917_ = v___x_953_;
                    v___y_918_ = v___y_941_;
                    v___y_919_ = v___y_943_;
                    v___y_920_ = v___y_942_;
                    v___y_921_ = v___x_955_;
                    v___y_922_ = v___x_954_;
                    v___y_923_ = v___y_937_;
                    v___y_924_ = v___y_950_;
                    v___y_925_ = v_wds_x3f_948_;
                    v___y_926_ = v___y_940_;
                    v___y_927_ = v___y_944_;
                    v___y_928_ = v___y_946_;
                    v___y_929_ = v___y_947_;
                    v___y_930_ = v___x_958_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v___x_972_ = l_Lean_Syntax_getArg(v___y_961_, v___y_965_);
                lean_dec(v___y_961_);
                v___x_973_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45;
                lean_inc(v___x_972_);
                v___x_974_ = l_Lean_Syntax_isOfKind(v___x_972_, v___x_973_);
                if v___x_974_ == 0 {
                    v___x_975_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46;
                    v___x_976_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47;
                    v___x_977_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40;
                    v___x_978_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48;
                    lean_inc(v___x_972_);
                    v___x_979_ = l_Lean_Syntax_isOfKind(v___x_972_, v___x_978_);
                    if v___x_979_ == 0 {
                        lean_dec(v___x_972_);
                        lean_dec(v_args_x3f_969_);
                        lean_dec(v___y_968_);
                        lean_dec(v___y_966_);
                        lean_dec(v___y_962_);
                        lean_dec(v___y_960_);
                        v___x_980_ =
                            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                        v___x_981_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_x_649_, v___x_980_, v___y_970_, v___y_971_,
                        );
                        lean_dec(v_x_649_);
                        return v___x_981_;
                    } else {
                        v___x_982_ = l_Lean_Syntax_getArg(v___x_972_, v___y_965_);
                        v___x_983_ =
                            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49;
                        lean_inc(v___x_982_);
                        v___x_984_ = l_Lean_Syntax_isOfKind(v___x_982_, v___x_983_);
                        if v___x_984_ == 0 {
                            lean_dec(v___x_982_);
                            lean_dec(v___x_972_);
                            lean_dec(v_args_x3f_969_);
                            lean_dec(v___y_968_);
                            lean_dec(v___y_966_);
                            lean_dec(v___y_962_);
                            lean_dec(v___y_960_);
                            v___x_985_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                            v___x_986_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_x_649_, v___x_985_, v___y_970_, v___y_971_,
                            );
                            lean_dec(v_x_649_);
                            return v___x_986_;
                        } else {
                            v___x_987_ = l_Lean_Syntax_getArg(v___x_982_, v___x_701_);
                            v___x_988_ = l_Lean_Syntax_matchesNull(v___x_987_, v___x_701_);
                            if v___x_988_ == 0 {
                                lean_dec(v___x_982_);
                                lean_dec(v___x_972_);
                                lean_dec(v_args_x3f_969_);
                                lean_dec(v___y_968_);
                                lean_dec(v___y_966_);
                                lean_dec(v___y_962_);
                                lean_dec(v___y_960_);
                                v___x_989_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                v___x_990_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_x_649_, v___x_989_, v___y_970_, v___y_971_,
                                );
                                lean_dec(v_x_649_);
                                return v___x_990_;
                            } else {
                                v___x_991_ = l_Lean_Syntax_getArg(v___x_982_, v___y_964_);
                                lean_dec(v___x_982_);
                                v___x_992_ = l_Lean_Syntax_matchesNull(v___x_991_, v___x_701_);
                                if v___x_992_ == 0 {
                                    lean_dec(v___x_972_);
                                    lean_dec(v_args_x3f_969_);
                                    lean_dec(v___y_968_);
                                    lean_dec(v___y_966_);
                                    lean_dec(v___y_962_);
                                    lean_dec(v___y_960_);
                                    v___x_993_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                    v___x_994_ = l_Lean_Macro_throwErrorAt___redArg(
                                        v_x_649_, v___x_993_, v___y_970_, v___y_971_,
                                    );
                                    lean_dec(v_x_649_);
                                    return v___x_994_;
                                } else {
                                    v___x_995_ = l_Lean_Syntax_getArg(v___x_972_, v___y_964_);
                                    v___x_996_ = l_Lean_Syntax_getArg(v___x_972_, v___y_967_);
                                    lean_dec(v___x_972_);
                                    v___x_997_ = l_Lean_Syntax_isNone(v___x_996_);
                                    if v___x_997_ == 0 {
                                        lean_inc(v___x_996_);
                                        v___x_998_ =
                                            l_Lean_Syntax_matchesNull(v___x_996_, v___y_964_);
                                        if v___x_998_ == 0 {
                                            lean_dec(v___x_996_);
                                            lean_dec(v___x_995_);
                                            lean_dec(v_args_x3f_969_);
                                            lean_dec(v___y_968_);
                                            lean_dec(v___y_966_);
                                            lean_dec(v___y_962_);
                                            lean_dec(v___y_960_);
                                            v___x_999_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                            v___x_1000_ = l_Lean_Macro_throwErrorAt___redArg(
                                                v_x_649_, v___x_999_, v___y_970_, v___y_971_,
                                            );
                                            lean_dec(v_x_649_);
                                            return v___x_1000_;
                                        } else {
                                            v_wds_x3f_1001_ =
                                                l_Lean_Syntax_getArg(v___x_996_, v___x_701_);
                                            lean_dec(v___x_996_);
                                            v___x_1002_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51;
                                            lean_inc(v_wds_x3f_1001_);
                                            v___x_1003_ = l_Lean_Syntax_isOfKind(
                                                v_wds_x3f_1001_,
                                                v___x_1002_,
                                            );
                                            if v___x_1003_ == 0 {
                                                lean_dec(v_wds_x3f_1001_);
                                                lean_dec(v___x_995_);
                                                lean_dec(v_args_x3f_969_);
                                                lean_dec(v___y_968_);
                                                lean_dec(v___y_966_);
                                                lean_dec(v___y_962_);
                                                lean_dec(v___y_960_);
                                                v___x_1004_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                                v___x_1005_ = l_Lean_Macro_throwErrorAt___redArg(
                                                    v_x_649_,
                                                    v___x_1004_,
                                                    v___y_970_,
                                                    v___y_971_,
                                                );
                                                lean_dec(v_x_649_);
                                                return v___x_1005_;
                                            } else {
                                                lean_dec(v_x_649_);
                                                v___x_1006_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                lean_ctor_set(v___x_1006_, 0, v_wds_x3f_1001_);
                                                v___y_786_ = v___y_960_;
                                                v___y_787_ = v_args_x3f_969_;
                                                v___y_788_ = v___x_995_;
                                                v___y_789_ = v___y_964_;
                                                v___y_790_ = v___x_974_;
                                                v___y_791_ = v___y_966_;
                                                v___y_792_ = v___x_983_;
                                                v___y_793_ = v___x_977_;
                                                v___y_794_ = v___y_962_;
                                                v___y_795_ = v___x_975_;
                                                v___y_796_ = v___x_976_;
                                                v___y_797_ = v___y_965_;
                                                v___y_798_ = v___x_978_;
                                                v___y_799_ = v___y_968_;
                                                v_wds_x3f_800_ = v___x_1006_;
                                                v___y_801_ = v___y_970_;
                                                v___y_802_ = v___y_971_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v___x_996_);
                                        lean_dec(v_x_649_);
                                        v___x_1007_ = lean_box(0);
                                        v___y_786_ = v___y_960_;
                                        v___y_787_ = v_args_x3f_969_;
                                        v___y_788_ = v___x_995_;
                                        v___y_789_ = v___y_964_;
                                        v___y_790_ = v___x_974_;
                                        v___y_791_ = v___y_966_;
                                        v___y_792_ = v___x_983_;
                                        v___y_793_ = v___x_977_;
                                        v___y_794_ = v___y_962_;
                                        v___y_795_ = v___x_975_;
                                        v___y_796_ = v___x_976_;
                                        v___y_797_ = v___y_965_;
                                        v___y_798_ = v___x_978_;
                                        v___y_799_ = v___y_968_;
                                        v_wds_x3f_800_ = v___x_1007_;
                                        v___y_801_ = v___y_970_;
                                        v___y_802_ = v___y_971_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    v___x_1008_ = l_Lean_Syntax_getArg(v___x_972_, v___x_701_);
                    v___x_1009_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46;
                    v___x_1010_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47;
                    v___x_1011_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52;
                    v___x_1012_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53;
                    lean_inc(v___x_1008_);
                    v___x_1013_ = l_Lean_Syntax_isOfKind(v___x_1008_, v___x_1012_);
                    if v___x_1013_ == 0 {
                        lean_dec(v___x_1008_);
                        lean_dec(v___x_972_);
                        lean_dec(v_args_x3f_969_);
                        lean_dec(v___y_968_);
                        lean_dec(v___y_966_);
                        lean_dec(v___y_962_);
                        lean_dec(v___y_960_);
                        v___x_1014_ =
                            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                        v___x_1015_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_x_649_,
                            v___x_1014_,
                            v___y_970_,
                            v___y_971_,
                        );
                        lean_dec(v_x_649_);
                        return v___x_1015_;
                    } else {
                        v___x_1016_ = l_Lean_Syntax_getArg(v___x_1008_, v___y_964_);
                        lean_dec(v___x_1008_);
                        v___x_1017_ = l_Lean_Syntax_getArg(v___x_972_, v___y_964_);
                        lean_dec(v___x_972_);
                        v___x_1018_ = l_Lean_Syntax_isNone(v___x_1017_);
                        if v___x_1018_ == 0 {
                            lean_inc(v___x_1017_);
                            v___x_1019_ = l_Lean_Syntax_matchesNull(v___x_1017_, v___y_964_);
                            if v___x_1019_ == 0 {
                                lean_dec(v___x_1017_);
                                lean_dec(v___x_1016_);
                                lean_dec(v_args_x3f_969_);
                                lean_dec(v___y_968_);
                                lean_dec(v___y_966_);
                                lean_dec(v___y_962_);
                                lean_dec(v___y_960_);
                                v___x_1020_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                v___x_1021_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_x_649_,
                                    v___x_1020_,
                                    v___y_970_,
                                    v___y_971_,
                                );
                                lean_dec(v_x_649_);
                                return v___x_1021_;
                            } else {
                                v_wds_x3f_1022_ = l_Lean_Syntax_getArg(v___x_1017_, v___x_701_);
                                lean_dec(v___x_1017_);
                                v___x_1023_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51;
                                lean_inc(v_wds_x3f_1022_);
                                v___x_1024_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1022_, v___x_1023_);
                                if v___x_1024_ == 0 {
                                    lean_dec(v_wds_x3f_1022_);
                                    lean_dec(v___x_1016_);
                                    lean_dec(v_args_x3f_969_);
                                    lean_dec(v___y_968_);
                                    lean_dec(v___y_966_);
                                    lean_dec(v___y_962_);
                                    lean_dec(v___y_960_);
                                    v___x_1025_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                    v___x_1026_ = l_Lean_Macro_throwErrorAt___redArg(
                                        v_x_649_,
                                        v___x_1025_,
                                        v___y_970_,
                                        v___y_971_,
                                    );
                                    lean_dec(v_x_649_);
                                    return v___x_1026_;
                                } else {
                                    lean_dec(v_x_649_);
                                    v___x_1027_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_1027_, 0, v_wds_x3f_1022_);
                                    v___y_937_ = v___x_1011_;
                                    v___y_938_ = v___y_960_;
                                    v___y_939_ = v_args_x3f_969_;
                                    v___y_940_ = v___y_962_;
                                    v___y_941_ = v___y_963_;
                                    v___y_942_ = v___x_1010_;
                                    v___y_943_ = v___y_966_;
                                    v___y_944_ = v___x_1012_;
                                    v___y_945_ = v___y_968_;
                                    v___y_946_ = v___x_1016_;
                                    v___y_947_ = v___x_1009_;
                                    v_wds_x3f_948_ = v___x_1027_;
                                    v___y_949_ = v___y_970_;
                                    v___y_950_ = v___y_971_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_1017_);
                            lean_dec(v_x_649_);
                            v___x_1028_ = lean_box(0);
                            v___y_937_ = v___x_1011_;
                            v___y_938_ = v___y_960_;
                            v___y_939_ = v_args_x3f_969_;
                            v___y_940_ = v___y_962_;
                            v___y_941_ = v___y_963_;
                            v___y_942_ = v___x_1010_;
                            v___y_943_ = v___y_966_;
                            v___y_944_ = v___x_1012_;
                            v___y_945_ = v___y_968_;
                            v___y_946_ = v___x_1016_;
                            v___y_947_ = v___x_1009_;
                            v_wds_x3f_948_ = v___x_1028_;
                            v___y_949_ = v___y_970_;
                            v___y_950_ = v___y_971_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            12 => {
                v___x_1035_ = lean_unsigned_to_nat(3);
                v___x_1036_ = l_Lean_Syntax_getArg(v_x_649_, v___x_1035_);
                v___x_1037_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55;
                lean_inc(v___x_1036_);
                v___x_1038_ = l_Lean_Syntax_isOfKind(v___x_1036_, v___x_1037_);
                if v___x_1038_ == 0 {
                    lean_dec(v___x_1036_);
                    lean_dec(v_attrs_x3f_1032_);
                    lean_dec(v___y_1031_);
                    v___x_1039_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                    v___x_1040_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_x_649_,
                        v___x_1039_,
                        v___y_1033_,
                        v___y_1034_,
                    );
                    lean_dec(v_x_649_);
                    return v___x_1040_;
                } else {
                    v___x_1041_ = lean_unsigned_to_nat(2);
                    v_kw_1042_ = l_Lean_Syntax_getArg(v_x_649_, v___x_1041_);
                    v_name_1043_ = l_Lean_Syntax_getArg(v___x_1036_, v___x_701_);
                    v___x_1044_ = l_Lean_Syntax_getArg(v___x_1036_, v___y_1030_);
                    v___x_1045_ = l_Lean_Syntax_isNone(v___x_1044_);
                    if v___x_1045_ == 0 {
                        lean_inc(v___x_1044_);
                        v___x_1046_ = l_Lean_Syntax_matchesNull(v___x_1044_, v___y_1030_);
                        if v___x_1046_ == 0 {
                            lean_dec(v___x_1044_);
                            lean_dec(v_name_1043_);
                            lean_dec(v_kw_1042_);
                            lean_dec(v___x_1036_);
                            lean_dec(v_attrs_x3f_1032_);
                            lean_dec(v___y_1031_);
                            v___x_1047_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                            v___x_1048_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_x_649_,
                                v___x_1047_,
                                v___y_1033_,
                                v___y_1034_,
                            );
                            lean_dec(v_x_649_);
                            return v___x_1048_;
                        } else {
                            v_args_x3f_1049_ = l_Lean_Syntax_getArg(v___x_1044_, v___x_701_);
                            lean_dec(v___x_1044_);
                            v___x_1050_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1050_, 0, v_args_x3f_1049_);
                            v___y_960_ = v_kw_1042_;
                            v___y_961_ = v___x_1036_;
                            v___y_962_ = v_name_1043_;
                            v___y_963_ = v___x_1037_;
                            v___y_964_ = v___y_1030_;
                            v___y_965_ = v___x_1041_;
                            v___y_966_ = v_attrs_x3f_1032_;
                            v___y_967_ = v___x_1035_;
                            v___y_968_ = v___y_1031_;
                            v_args_x3f_969_ = v___x_1050_;
                            v___y_970_ = v___y_1033_;
                            v___y_971_ = v___y_1034_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1044_);
                        v___x_1051_ = lean_box(0);
                        v___y_960_ = v_kw_1042_;
                        v___y_961_ = v___x_1036_;
                        v___y_962_ = v_name_1043_;
                        v___y_963_ = v___x_1037_;
                        v___y_964_ = v___y_1030_;
                        v___y_965_ = v___x_1041_;
                        v___y_966_ = v_attrs_x3f_1032_;
                        v___y_967_ = v___x_1035_;
                        v___y_968_ = v___y_1031_;
                        v_args_x3f_969_ = v___x_1051_;
                        v___y_970_ = v___y_1033_;
                        v___y_971_ = v___y_1034_;
                        state = 11;
                        continue;
                    }
                }
            }
            13 => {
                v___x_1056_ = lean_unsigned_to_nat(1);
                v___x_1057_ = l_Lean_Syntax_getArg(v_x_649_, v___x_1056_);
                v___x_1058_ = l_Lean_Syntax_isNone(v___x_1057_);
                if v___x_1058_ == 0 {
                    lean_inc(v___x_1057_);
                    v___x_1059_ = l_Lean_Syntax_matchesNull(v___x_1057_, v___x_1056_);
                    if v___x_1059_ == 0 {
                        lean_dec(v___x_1057_);
                        lean_dec(v_doc_x3f_1053_);
                        v___x_1060_ =
                            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                        v___x_1061_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_x_649_,
                            v___x_1060_,
                            v___y_1054_,
                            v___y_1055_,
                        );
                        lean_dec(v_x_649_);
                        return v___x_1061_;
                    } else {
                        v_attrs_x3f_1062_ = l_Lean_Syntax_getArg(v___x_1057_, v___x_701_);
                        lean_dec(v___x_1057_);
                        v___x_1063_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1063_, 0, v_attrs_x3f_1062_);
                        v___y_1030_ = v___x_1056_;
                        v___y_1031_ = v_doc_x3f_1053_;
                        v_attrs_x3f_1032_ = v___x_1063_;
                        v___y_1033_ = v___y_1054_;
                        v___y_1034_ = v___y_1055_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1057_);
                    v___x_1064_ = lean_box(0);
                    v___y_1030_ = v___x_1056_;
                    v___y_1031_ = v_doc_x3f_1053_;
                    v_attrs_x3f_1032_ = v___x_1064_;
                    v___y_1033_ = v___y_1054_;
                    v___y_1034_ = v___y_1055_;
                    state = 12;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___boxed(
    mut v_x_1074_: *mut LeanObject,
    mut v_a_1075_: *mut LeanObject,
    mut v_a_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1077_: *mut LeanObject = core::ptr::null_mut();
    v_res_1077_ =
        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl(v_x_1074_, v_a_1075_, v_a_1076_);
    lean_dec_ref(v_a_1075_);
    return v_res_1077_;
}
pub unsafe fn l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1()
-> *mut LeanObject {
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    v___x_1106_ = l_Lean_Elab_macroAttribute;
    v___x_1107_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3;
    v___x_1108_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10;
    v___x_1109_ = lean_alloc_closure(
        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_1110_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1106_,
        v___x_1107_,
        v___x_1108_,
        v___x_1109_,
    );
    return v___x_1110_;
}
pub unsafe fn l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___boxed(
    mut v_a_1111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1112_: *mut LeanObject = core::ptr::null_mut();
    v_res_1112_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
    return v_res_1112_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Script(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Script(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Script(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_DSL_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_DSL_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Script(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Script(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_DSL_Script(builtin);
}

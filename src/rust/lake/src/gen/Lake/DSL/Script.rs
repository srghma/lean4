// Lean compiler output
// Module: Lake.DSL.Script
// Imports: Init.Prelude Lake.Config.Package Lake.DSL.Attributes Lake.DSL.Syntax
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_SepArray_ofElems, l_Lean_Syntax_isNone};
use crate::r#gen::Init::Prelude::{
    initialize_Init_Prelude, l_Array_mkArray0, l_Array_mkArray1___redArg,
    l_Lean_Macro_throwErrorAt___redArg, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node7, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
    runtime_initialize_Init_Prelude,
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
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value)
        as *mut leanh::LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value
        ) as *mut leanh::LeanObject,
        5901868804703194544 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value
        ) as *mut leanh::LeanObject,
        11447824861308129923 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7_value:
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
    m_data: [44, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8_value:
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
    m_data: [93, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15_value:
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
    m_data: [58, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value
        ) as *mut leanh::LeanObject,
        10003671174329666725 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18_value
) as *mut leanh::LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value
        ) as *mut leanh::LeanObject,
        16942896190233842921 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25_value:
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27_value:
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
    m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29_value
        ) as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36_value
        ) as *mut leanh::LeanObject,
        887671011676595348 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38_value:
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
    m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39_value:
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
        100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40_value:
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
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41_value:
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
        100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42_value:
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
    m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44_value
) as *mut leanh::LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value
        ) as *mut leanh::LeanObject,
        5901868804703194544 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44_value
        ) as *mut leanh::LeanObject,
        11022427548561232637 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value
) as *mut leanh::LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_2:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40_value
        ) as *mut leanh::LeanObject,
        17342580262104060118 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41_value
        ) as *mut leanh::LeanObject,
        13585030837571646948 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value
) as *mut leanh::LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_2:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42_value
        ) as *mut leanh::LeanObject,
        7625897890118033792 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43_value
        ) as *mut leanh::LeanObject,
        8715860392475343861 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50_value
) as *mut leanh::LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_2:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value
        ) as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50_value
        ) as *mut leanh::LeanObject,
        4503069825835506739 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52_value
) as *mut leanh::LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_2:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value
        ) as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52_value
        ) as *mut leanh::LeanObject,
        5817315006727311029 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54_value
) as *mut leanh::LeanObject;
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value
        ) as *mut leanh::LeanObject,
        5901868804703194544 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54_value
        ) as *mut leanh::LeanObject,
        7959617833543045482 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value) as *mut leanh::LeanObject,12997130533650095963 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value) as *mut leanh::LeanObject,11286550318989764116 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 99, 114, 105, 112, 116, 0]};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4_value) as *mut leanh::LeanObject,6321669005470951828 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,1573984873544968597 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value) as *mut leanh::LeanObject,15189868043128492961 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value) as *mut leanh::LeanObject,1611460809877233174 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 120, 112, 97, 110, 100, 83, 99, 114, 105, 112, 116, 68, 101, 99, 108, 0]};
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9_value) as *mut leanh::LeanObject,11098910053431617253 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_578_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16;
    v___x_579_ = l_String_toRawSubstring_x27(v___x_578_);
    return v___x_579_;
}
pub unsafe fn _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_600_;
}
pub unsafe fn _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_604_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34;
    v___x_605_ = l_String_toRawSubstring_x27(v___x_604_);
    return v___x_605_;
}
pub unsafe fn l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl(
    mut v_x_649_: *mut leanh::LeanObject,
    mut v_a_650_: *mut leanh::LeanObject,
    mut v_a_651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u8 = 0;
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_790_: u8 = 0;
    let mut v___y_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_850_: u8 = 0;
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_854_: u8 = 0;
    let mut v___y_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: u8 = 0;
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_x3f_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: u8 = 0;
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u8 = 0;
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: u8 = 0;
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: u8 = 0;
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: u8 = 0;
    let mut v___x_998_: u8 = 0;
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: u8 = 0;
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: u8 = 0;
    let mut v___x_1019_: u8 = 0;
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: u8 = 0;
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: u8 = 0;
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kw_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: u8 = 0;
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_x3f_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: u8 = 0;
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_675_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3;
                leanh::lean_inc(v_x_649_);
                v___x_698_ = l_Lean_Syntax_isOfKind(v_x_649_, v___x_675_);
                if v___x_698_ == 0 {
                    v___x_699_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                    v___x_700_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_x_649_, v___x_699_, v_a_650_, v_a_651_,
                    );
                    leanh::lean_dec(v_x_649_);
                    return v___x_700_;
                } else {
                    v___x_701_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1065_ = l_Lean_Syntax_getArg(v_x_649_, v___x_701_);
                    v___x_1066_ = l_Lean_Syntax_isNone(v___x_1065_);
                    if v___x_1066_ == 0 {
                        v___x_1067_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_1065_);
                        v___x_1068_ = l_Lean_Syntax_matchesNull(v___x_1065_, v___x_1067_);
                        if v___x_1068_ == 0 {
                            leanh::lean_dec(v___x_1065_);
                            v___x_1069_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                            v___x_1070_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_x_649_,
                                v___x_1069_,
                                v_a_650_,
                                v_a_651_,
                            );
                            leanh::lean_dec(v_x_649_);
                            return v___x_1070_;
                        } else {
                            v_doc_x3f_1071_ = l_Lean_Syntax_getArg(v___x_1065_, v___x_701_);
                            leanh::lean_dec(v___x_1065_);
                            v___x_1072_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1072_, 0, v_doc_x3f_1071_);
                            v_doc_x3f_1053_ = v___x_1072_;
                            v___y_1054_ = v_a_650_;
                            v___y_1055_ = v_a_651_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1065_);
                        v___x_1073_ = leanh::lean_box(0);
                        v_doc_x3f_1053_ = v___x_1073_;
                        v___y_1054_ = v_a_650_;
                        v___y_1055_ = v_a_651_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_666_);
                v___x_669_ = l_Array_append___redArg(v___y_666_, v___y_668_);
                leanh::lean_dec_ref(v___y_668_);
                leanh::lean_inc(v___y_667_);
                leanh::lean_inc_n(v___y_663_, 3);
                v___x_670_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_670_, 0, v___y_663_);
                leanh::lean_ctor_set(v___x_670_, 1, v___y_667_);
                leanh::lean_ctor_set(v___x_670_, 2, v___x_669_);
                leanh::lean_inc(v___y_664_);
                v___x_671_ = l_Lean_Syntax_node4(
                    v___y_663_, v___y_664_, v___y_661_, v___y_662_, v___y_665_, v___x_670_,
                );
                v___x_672_ = l_Lean_Syntax_node5(
                    v___y_663_, v___y_654_, v___y_656_, v___y_659_, v___y_653_, v___x_671_,
                    v___y_657_,
                );
                v___x_673_ = l_Lean_Syntax_node2(v___y_663_, v___y_660_, v___y_658_, v___x_672_);
                v___x_674_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_674_, 0, v___x_673_);
                leanh::lean_ctor_set(v___x_674_, 1, v___y_655_);
                return v___x_674_;
            }
            2 => {
                leanh::lean_inc_ref(v___y_682_);
                v___x_692_ = l_Array_append___redArg(v___y_682_, v___y_691_);
                leanh::lean_dec_ref(v___y_691_);
                leanh::lean_inc(v___y_683_);
                leanh::lean_inc_n(v___y_678_, 3);
                v___x_693_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_693_, 0, v___y_678_);
                leanh::lean_ctor_set(v___x_693_, 1, v___y_683_);
                leanh::lean_ctor_set(v___x_693_, 2, v___x_692_);
                v___x_694_ = l_Lean_Syntax_node4(
                    v___y_678_, v___y_689_, v___y_687_, v___y_681_, v___y_677_, v___x_693_,
                );
                leanh::lean_inc(v___y_679_);
                v___x_695_ =
                    l_Lean_Syntax_node3(v___y_678_, v___y_679_, v___y_686_, v___y_688_, v___x_694_);
                v___x_696_ = l_Lean_Syntax_node4(
                    v___y_678_, v___x_675_, v___y_690_, v___y_685_, v___y_680_, v___x_695_,
                );
                v___x_697_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_697_, 0, v___x_696_);
                leanh::lean_ctor_set(v___x_697_, 1, v___y_684_);
                return v___x_697_;
            }
            3 => {
                leanh::lean_inc_ref_n(v___y_722_, 2);
                v___x_726_ = l_Array_append___redArg(v___y_722_, v___y_725_);
                leanh::lean_dec_ref(v___y_725_);
                leanh::lean_inc_n(v___y_723_, 6);
                leanh::lean_inc_n(v___y_720_, 20);
                v___x_727_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_727_, 0, v___y_720_);
                leanh::lean_ctor_set(v___x_727_, 1, v___y_723_);
                leanh::lean_ctor_set(v___x_727_, 2, v___x_726_);
                v___x_728_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5;
                leanh::lean_inc_ref_n(v___y_717_, 3);
                leanh::lean_inc_ref_n(v___y_715_, 7);
                leanh::lean_inc_ref_n(v___y_714_, 7);
                v___x_729_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_717_, v___x_728_);
                v___x_730_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6;
                v___x_731_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_731_, 0, v___y_720_);
                leanh::lean_ctor_set(v___x_731_, 1, v___x_730_);
                v___x_732_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7;
                v___x_733_ = l_Lean_Syntax_SepArray_ofElems(v___x_732_, v___y_713_);
                leanh::lean_dec_ref(v___y_713_);
                v___x_734_ = l_Array_append___redArg(v___y_722_, v___x_733_);
                leanh::lean_dec_ref(v___x_733_);
                v___x_735_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_735_, 0, v___y_720_);
                leanh::lean_ctor_set(v___x_735_, 1, v___y_723_);
                leanh::lean_ctor_set(v___x_735_, 2, v___x_734_);
                v___x_736_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8;
                v___x_737_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_737_, 0, v___y_720_);
                leanh::lean_ctor_set(v___x_737_, 1, v___x_736_);
                v___x_738_ =
                    l_Lean_Syntax_node3(v___y_720_, v___x_729_, v___x_731_, v___x_735_, v___x_737_);
                v___x_739_ = l_Lean_Syntax_node1(v___y_720_, v___y_723_, v___x_738_);
                leanh::lean_inc_n(v___y_708_, 9);
                v___x_740_ = l_Lean_Syntax_node7(
                    v___y_720_, v___y_710_, v___x_727_, v___x_739_, v___y_708_, v___y_708_,
                    v___y_708_, v___y_708_, v___y_708_,
                );
                v___x_741_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9;
                leanh::lean_inc_ref_n(v___y_712_, 3);
                v___x_742_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_712_, v___x_741_);
                v___x_743_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10;
                v___x_744_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_744_, 0, v___y_720_);
                leanh::lean_ctor_set(v___x_744_, 1, v___x_743_);
                v___x_745_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11;
                v___x_746_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_712_, v___x_745_);
                v___x_747_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12;
                v___x_748_ = leanh::lean_box(2);
                v___x_749_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_749_, 0, v___x_748_);
                leanh::lean_ctor_set(v___x_749_, 1, v___y_723_);
                leanh::lean_ctor_set(v___x_749_, 2, v___x_747_);
                v___x_750_ = lean_mk_empty_array_with_capacity(v___y_719_);
                v___x_751_ = lean_array_push(v___x_750_, v___y_716_);
                v___x_752_ = lean_array_push(v___x_751_, v___x_749_);
                v___x_753_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_753_, 0, v___x_748_);
                leanh::lean_ctor_set(v___x_753_, 1, v___x_746_);
                leanh::lean_ctor_set(v___x_753_, 2, v___x_752_);
                v___x_754_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13;
                v___x_755_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_712_, v___x_754_);
                v___x_756_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14;
                v___x_757_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_717_, v___x_756_);
                v___x_758_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15;
                v___x_759_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_759_, 0, v___y_720_);
                leanh::lean_ctor_set(v___x_759_, 1, v___x_758_);
                v___x_760_ = leanh::lean_obj_once(
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
                leanh::lean_inc(v___y_724_);
                v___x_764_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_764_, 0, v___x_763_);
                leanh::lean_ctor_set(v___x_764_, 1, v___y_724_);
                v___x_765_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_765_, 0, v___y_720_);
                leanh::lean_ctor_set(v___x_765_, 1, v___x_760_);
                leanh::lean_ctor_set(v___x_765_, 2, v___x_762_);
                leanh::lean_ctor_set(v___x_765_, 3, v___x_764_);
                v___x_766_ = l_Lean_Syntax_node2(v___y_720_, v___x_757_, v___x_759_, v___x_765_);
                v___x_767_ = l_Lean_Syntax_node1(v___y_720_, v___y_723_, v___x_766_);
                v___x_768_ = l_Lean_Syntax_node2(v___y_720_, v___x_755_, v___y_708_, v___x_767_);
                v___x_769_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21;
                v___x_770_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_770_, 0, v___y_720_);
                leanh::lean_ctor_set(v___x_770_, 1, v___x_769_);
                v___x_771_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22;
                v___x_772_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_717_, v___x_771_);
                v___x_773_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_773_, 0, v___y_720_);
                leanh::lean_ctor_set(v___x_773_, 1, v___x_771_);
                v___x_774_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23;
                v___x_775_ = l_Lean_Name_mkStr4(v___y_714_, v___y_715_, v___y_717_, v___x_774_);
                v___x_776_ = l_Lean_Syntax_node1(v___y_720_, v___y_723_, v___y_718_);
                v___x_777_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24;
                v___x_778_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_778_, 0, v___y_720_);
                leanh::lean_ctor_set(v___x_778_, 1, v___x_777_);
                v___x_779_ = l_Lean_Syntax_node4(
                    v___y_720_, v___x_775_, v___x_776_, v___y_708_, v___x_778_, v___y_707_,
                );
                v___x_780_ = l_Lean_Syntax_node2(v___y_720_, v___x_772_, v___x_773_, v___x_779_);
                leanh::lean_inc(v___y_709_);
                v___x_781_ = l_Lean_Syntax_node2(v___y_720_, v___y_709_, v___y_708_, v___y_708_);
                if leanh::lean_obj_tag(v___y_703_) == 1 {
                    v_val_782_ = leanh::lean_ctor_get(v___y_703_, 0);
                    leanh::lean_inc(v_val_782_);
                    leanh::lean_dec_ref_known(v___y_703_, 1);
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
                    leanh::lean_dec(v___y_703_);
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
                v_methods_803_ = leanh::lean_ctor_get(v___y_801_, 0);
                v_quotContext_804_ = leanh::lean_ctor_get(v___y_801_, 1);
                v_currMacroScope_805_ = leanh::lean_ctor_get(v___y_801_, 2);
                v_currRecDepth_806_ = leanh::lean_ctor_get(v___y_801_, 3);
                v_maxRecDepth_807_ = leanh::lean_ctor_get(v___y_801_, 4);
                v_ref_808_ = leanh::lean_ctor_get(v___y_801_, 5);
                v_ref_809_ = l_Lean_replaceRef(v___y_786_, v_ref_808_);
                leanh::lean_dec(v___y_786_);
                leanh::lean_inc(v_ref_809_);
                leanh::lean_inc(v_maxRecDepth_807_);
                leanh::lean_inc(v_currRecDepth_806_);
                leanh::lean_inc(v_currMacroScope_805_);
                leanh::lean_inc(v_quotContext_804_);
                leanh::lean_inc(v_methods_803_);
                v___x_810_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_810_, 0, v_methods_803_);
                leanh::lean_ctor_set(v___x_810_, 1, v_quotContext_804_);
                leanh::lean_ctor_set(v___x_810_, 2, v_currMacroScope_805_);
                leanh::lean_ctor_set(v___x_810_, 3, v_currRecDepth_806_);
                leanh::lean_ctor_set(v___x_810_, 4, v_maxRecDepth_807_);
                leanh::lean_ctor_set(v___x_810_, 5, v_ref_809_);
                v___x_811_ = l_Lake_DSL_expandOptSimpleBinder(v___y_787_, v___x_810_, v___y_802_);
                leanh::lean_dec_ref_known(v___x_810_, 6);
                if leanh::lean_obj_tag(v___x_811_) == 0 {
                    v_a_812_ = leanh::lean_ctor_get(v___x_811_, 0);
                    leanh::lean_inc(v_a_812_);
                    v_a_813_ = leanh::lean_ctor_get(v___x_811_, 1);
                    leanh::lean_inc(v_a_813_);
                    leanh::lean_dec_ref_known(v___x_811_, 2);
                    v_id_814_ = l_Lake_DSL_expandIdentOrStrAsIdent(v___y_794_);
                    v___x_815_ = l_Lean_SourceInfo_fromRef(v_ref_809_, v___y_790_);
                    leanh::lean_dec(v_ref_809_);
                    v___x_816_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26;
                    v___x_817_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27;
                    leanh::lean_inc_ref_n(v___y_796_, 5);
                    leanh::lean_inc_ref_n(v___y_795_, 5);
                    v___x_818_ = l_Lean_Name_mkStr4(v___y_795_, v___y_796_, v___x_816_, v___x_817_);
                    v___x_819_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28;
                    v___x_820_ = l_Lean_Name_mkStr4(v___y_795_, v___y_796_, v___x_816_, v___x_819_);
                    v___x_821_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30;
                    v___x_822_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31), core::ptr::addr_of_mut!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once), _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31);
                    leanh::lean_inc_n(v___x_815_, 5);
                    v___x_823_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_823_, 0, v___x_815_);
                    leanh::lean_ctor_set(v___x_823_, 1, v___x_821_);
                    leanh::lean_ctor_set(v___x_823_, 2, v___x_822_);
                    leanh::lean_inc_ref_n(v___x_823_, 2);
                    v___x_824_ = l_Lean_Syntax_node1(v___x_815_, v___x_820_, v___x_823_);
                    v___x_825_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32;
                    v___x_826_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33;
                    v___x_827_ = l_Lean_Name_mkStr4(v___y_795_, v___y_796_, v___x_825_, v___x_826_);
                    v___x_828_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35), core::ptr::addr_of_mut!(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35_once), _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35);
                    v___x_829_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37;
                    leanh::lean_inc(v_currMacroScope_805_);
                    leanh::lean_inc(v_quotContext_804_);
                    v___x_830_ =
                        l_Lean_addMacroScope(v_quotContext_804_, v___x_829_, v_currMacroScope_805_);
                    v___x_831_ = leanh::lean_box(0);
                    v___x_832_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_832_, 0, v___x_815_);
                    leanh::lean_ctor_set(v___x_832_, 1, v___x_828_);
                    leanh::lean_ctor_set(v___x_832_, 2, v___x_830_);
                    leanh::lean_ctor_set(v___x_832_, 3, v___x_831_);
                    v___x_833_ =
                        l_Lean_Syntax_node2(v___x_815_, v___x_827_, v___x_832_, v___x_823_);
                    v___x_834_ =
                        l_Lean_Syntax_node2(v___x_815_, v___x_818_, v___x_824_, v___x_833_);
                    v___x_835_ = lean_mk_empty_array_with_capacity(v___y_789_);
                    v___x_836_ = lean_array_push(v___x_835_, v___x_834_);
                    v___x_837_ = l_Lake_DSL_expandAttrs(v___y_791_);
                    v___x_838_ = l_Array_append___redArg(v___x_836_, v___x_837_);
                    leanh::lean_dec_ref(v___x_837_);
                    v___x_839_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38;
                    leanh::lean_inc_ref_n(v___y_793_, 2);
                    v___x_840_ = l_Lean_Name_mkStr4(v___y_795_, v___y_796_, v___y_793_, v___x_839_);
                    v___x_841_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39;
                    v___x_842_ = l_Lean_Name_mkStr4(v___y_795_, v___y_796_, v___y_793_, v___x_841_);
                    if leanh::lean_obj_tag(v___y_799_) == 1 {
                        v_val_843_ = leanh::lean_ctor_get(v___y_799_, 0);
                        leanh::lean_inc(v_val_843_);
                        leanh::lean_dec_ref_known(v___y_799_, 1);
                        v___x_844_ = l_Array_mkArray1___redArg(v_val_843_);
                        leanh::lean_inc(v_quotContext_804_);
                        leanh::lean_inc(v_currMacroScope_805_);
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
                        leanh::lean_dec(v___y_799_);
                        v___x_845_ =
                            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
                        leanh::lean_inc(v_quotContext_804_);
                        leanh::lean_inc(v_currMacroScope_805_);
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
                    leanh::lean_dec(v_ref_809_);
                    leanh::lean_dec(v_wds_x3f_800_);
                    leanh::lean_dec(v___y_799_);
                    leanh::lean_dec(v___y_794_);
                    leanh::lean_dec(v___y_791_);
                    leanh::lean_dec(v___y_788_);
                    v_a_846_ = leanh::lean_ctor_get(v___x_811_, 0);
                    v_a_847_ = leanh::lean_ctor_get(v___x_811_, 1);
                    v_isSharedCheck_854_ = (!leanh::lean_is_exclusive(v___x_811_)) as u8;
                    if v_isSharedCheck_854_ == 0 {
                        v___x_849_ = v___x_811_;
                        v_isShared_850_ = v_isSharedCheck_854_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_847_);
                        leanh::lean_inc(v_a_846_);
                        leanh::lean_dec(v___x_811_);
                        v___x_849_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_853_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_846_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_853_, 1, v_a_847_);
                    v___x_852_ = v_reuseFailAlloc_853_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_852_;
            }
            7 => {
                leanh::lean_inc_ref_n(v___y_860_, 2);
                v___x_872_ = l_Array_append___redArg(v___y_860_, v___y_871_);
                leanh::lean_dec_ref(v___y_871_);
                leanh::lean_inc_n(v___y_861_, 2);
                leanh::lean_inc_n(v___y_856_, 6);
                v___x_873_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_873_, 0, v___y_856_);
                leanh::lean_ctor_set(v___x_873_, 1, v___y_861_);
                leanh::lean_ctor_set(v___x_873_, 2, v___x_872_);
                v___x_874_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40;
                v___x_875_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41;
                leanh::lean_inc_ref_n(v___y_859_, 2);
                leanh::lean_inc_ref_n(v___y_870_, 2);
                v___x_876_ = l_Lean_Name_mkStr4(v___y_870_, v___y_859_, v___x_874_, v___x_875_);
                v___x_877_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21;
                v___x_878_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_878_, 0, v___y_856_);
                leanh::lean_ctor_set(v___x_878_, 1, v___x_877_);
                leanh::lean_inc_ref(v___y_862_);
                v___x_879_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_879_, 0, v___y_856_);
                leanh::lean_ctor_set(v___x_879_, 1, v___y_862_);
                leanh::lean_inc(v___y_868_);
                v___x_880_ = l_Lean_Syntax_node2(v___y_856_, v___y_868_, v___x_879_, v___y_869_);
                v___x_881_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42;
                v___x_882_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43;
                v___x_883_ = l_Lean_Name_mkStr4(v___y_870_, v___y_859_, v___x_881_, v___x_882_);
                v___x_884_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_884_, 0, v___y_856_);
                leanh::lean_ctor_set(v___x_884_, 1, v___y_861_);
                leanh::lean_ctor_set(v___x_884_, 2, v___y_860_);
                leanh::lean_inc_ref(v___x_884_);
                v___x_885_ = l_Lean_Syntax_node2(v___y_856_, v___x_883_, v___x_884_, v___x_884_);
                if leanh::lean_obj_tag(v___y_864_) == 1 {
                    v_val_886_ = leanh::lean_ctor_get(v___y_864_, 0);
                    leanh::lean_inc(v_val_886_);
                    leanh::lean_dec_ref_known(v___y_864_, 1);
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
                    leanh::lean_dec(v___y_864_);
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
                leanh::lean_inc_ref(v___y_895_);
                v___x_906_ = l_Array_append___redArg(v___y_895_, v___y_905_);
                leanh::lean_dec_ref(v___y_905_);
                leanh::lean_inc(v___y_896_);
                leanh::lean_inc(v___y_892_);
                v___x_907_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_907_, 0, v___y_892_);
                leanh::lean_ctor_set(v___x_907_, 1, v___y_896_);
                leanh::lean_ctor_set(v___x_907_, 2, v___x_906_);
                v___x_908_ = l_Lean_SourceInfo_fromRef(v___y_891_, v___x_698_);
                leanh::lean_dec(v___y_891_);
                v___x_909_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36;
                v___x_910_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_910_, 0, v___x_908_);
                leanh::lean_ctor_set(v___x_910_, 1, v___x_909_);
                if leanh::lean_obj_tag(v___y_890_) == 1 {
                    v_val_911_ = leanh::lean_ctor_get(v___y_890_, 0);
                    leanh::lean_inc(v_val_911_);
                    leanh::lean_dec_ref_known(v___y_890_, 1);
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
                    leanh::lean_dec(v___y_890_);
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
                leanh::lean_inc_ref(v___y_921_);
                v___x_931_ = l_Array_append___redArg(v___y_921_, v___y_930_);
                leanh::lean_dec_ref(v___y_930_);
                leanh::lean_inc(v___y_922_);
                leanh::lean_inc(v___y_917_);
                v___x_932_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_932_, 0, v___y_917_);
                leanh::lean_ctor_set(v___x_932_, 1, v___y_922_);
                leanh::lean_ctor_set(v___x_932_, 2, v___x_931_);
                if leanh::lean_obj_tag(v___y_919_) == 1 {
                    v_val_933_ = leanh::lean_ctor_get(v___y_919_, 0);
                    leanh::lean_inc(v_val_933_);
                    leanh::lean_dec_ref_known(v___y_919_, 1);
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
                    leanh::lean_dec(v___y_919_);
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
                v_ref_951_ = leanh::lean_ctor_get(v___y_949_, 5);
                v___x_952_ = 0;
                v___x_953_ = l_Lean_SourceInfo_fromRef(v_ref_951_, v___x_952_);
                v___x_954_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30;
                v___x_955_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once
                    ),
                    _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31,
                );
                if leanh::lean_obj_tag(v___y_945_) == 1 {
                    v_val_956_ = leanh::lean_ctor_get(v___y_945_, 0);
                    leanh::lean_inc(v_val_956_);
                    leanh::lean_dec_ref_known(v___y_945_, 1);
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
                    leanh::lean_dec(v___y_945_);
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
                leanh::lean_dec(v___y_961_);
                v___x_973_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45;
                leanh::lean_inc(v___x_972_);
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
                    leanh::lean_inc(v___x_972_);
                    v___x_979_ = l_Lean_Syntax_isOfKind(v___x_972_, v___x_978_);
                    if v___x_979_ == 0 {
                        leanh::lean_dec(v___x_972_);
                        leanh::lean_dec(v_args_x3f_969_);
                        leanh::lean_dec(v___y_968_);
                        leanh::lean_dec(v___y_966_);
                        leanh::lean_dec(v___y_962_);
                        leanh::lean_dec(v___y_960_);
                        v___x_980_ =
                            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                        v___x_981_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_x_649_, v___x_980_, v___y_970_, v___y_971_,
                        );
                        leanh::lean_dec(v_x_649_);
                        return v___x_981_;
                    } else {
                        v___x_982_ = l_Lean_Syntax_getArg(v___x_972_, v___y_965_);
                        v___x_983_ =
                            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49;
                        leanh::lean_inc(v___x_982_);
                        v___x_984_ = l_Lean_Syntax_isOfKind(v___x_982_, v___x_983_);
                        if v___x_984_ == 0 {
                            leanh::lean_dec(v___x_982_);
                            leanh::lean_dec(v___x_972_);
                            leanh::lean_dec(v_args_x3f_969_);
                            leanh::lean_dec(v___y_968_);
                            leanh::lean_dec(v___y_966_);
                            leanh::lean_dec(v___y_962_);
                            leanh::lean_dec(v___y_960_);
                            v___x_985_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                            v___x_986_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_x_649_, v___x_985_, v___y_970_, v___y_971_,
                            );
                            leanh::lean_dec(v_x_649_);
                            return v___x_986_;
                        } else {
                            v___x_987_ = l_Lean_Syntax_getArg(v___x_982_, v___x_701_);
                            v___x_988_ = l_Lean_Syntax_matchesNull(v___x_987_, v___x_701_);
                            if v___x_988_ == 0 {
                                leanh::lean_dec(v___x_982_);
                                leanh::lean_dec(v___x_972_);
                                leanh::lean_dec(v_args_x3f_969_);
                                leanh::lean_dec(v___y_968_);
                                leanh::lean_dec(v___y_966_);
                                leanh::lean_dec(v___y_962_);
                                leanh::lean_dec(v___y_960_);
                                v___x_989_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                v___x_990_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_x_649_, v___x_989_, v___y_970_, v___y_971_,
                                );
                                leanh::lean_dec(v_x_649_);
                                return v___x_990_;
                            } else {
                                v___x_991_ = l_Lean_Syntax_getArg(v___x_982_, v___y_964_);
                                leanh::lean_dec(v___x_982_);
                                v___x_992_ = l_Lean_Syntax_matchesNull(v___x_991_, v___x_701_);
                                if v___x_992_ == 0 {
                                    leanh::lean_dec(v___x_972_);
                                    leanh::lean_dec(v_args_x3f_969_);
                                    leanh::lean_dec(v___y_968_);
                                    leanh::lean_dec(v___y_966_);
                                    leanh::lean_dec(v___y_962_);
                                    leanh::lean_dec(v___y_960_);
                                    v___x_993_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                    v___x_994_ = l_Lean_Macro_throwErrorAt___redArg(
                                        v_x_649_, v___x_993_, v___y_970_, v___y_971_,
                                    );
                                    leanh::lean_dec(v_x_649_);
                                    return v___x_994_;
                                } else {
                                    v___x_995_ = l_Lean_Syntax_getArg(v___x_972_, v___y_964_);
                                    v___x_996_ = l_Lean_Syntax_getArg(v___x_972_, v___y_967_);
                                    leanh::lean_dec(v___x_972_);
                                    v___x_997_ = l_Lean_Syntax_isNone(v___x_996_);
                                    if v___x_997_ == 0 {
                                        leanh::lean_inc(v___x_996_);
                                        v___x_998_ =
                                            l_Lean_Syntax_matchesNull(v___x_996_, v___y_964_);
                                        if v___x_998_ == 0 {
                                            leanh::lean_dec(v___x_996_);
                                            leanh::lean_dec(v___x_995_);
                                            leanh::lean_dec(v_args_x3f_969_);
                                            leanh::lean_dec(v___y_968_);
                                            leanh::lean_dec(v___y_966_);
                                            leanh::lean_dec(v___y_962_);
                                            leanh::lean_dec(v___y_960_);
                                            v___x_999_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                            v___x_1000_ = l_Lean_Macro_throwErrorAt___redArg(
                                                v_x_649_, v___x_999_, v___y_970_, v___y_971_,
                                            );
                                            leanh::lean_dec(v_x_649_);
                                            return v___x_1000_;
                                        } else {
                                            v_wds_x3f_1001_ =
                                                l_Lean_Syntax_getArg(v___x_996_, v___x_701_);
                                            leanh::lean_dec(v___x_996_);
                                            v___x_1002_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51;
                                            leanh::lean_inc(v_wds_x3f_1001_);
                                            v___x_1003_ = l_Lean_Syntax_isOfKind(
                                                v_wds_x3f_1001_,
                                                v___x_1002_,
                                            );
                                            if v___x_1003_ == 0 {
                                                leanh::lean_dec(v_wds_x3f_1001_);
                                                leanh::lean_dec(v___x_995_);
                                                leanh::lean_dec(v_args_x3f_969_);
                                                leanh::lean_dec(v___y_968_);
                                                leanh::lean_dec(v___y_966_);
                                                leanh::lean_dec(v___y_962_);
                                                leanh::lean_dec(v___y_960_);
                                                v___x_1004_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                                v___x_1005_ = l_Lean_Macro_throwErrorAt___redArg(
                                                    v_x_649_,
                                                    v___x_1004_,
                                                    v___y_970_,
                                                    v___y_971_,
                                                );
                                                leanh::lean_dec(v_x_649_);
                                                return v___x_1005_;
                                            } else {
                                                leanh::lean_dec(v_x_649_);
                                                v___x_1006_ =
                                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_1006_,
                                                    0,
                                                    v_wds_x3f_1001_,
                                                );
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
                                        leanh::lean_dec(v___x_996_);
                                        leanh::lean_dec(v_x_649_);
                                        v___x_1007_ = leanh::lean_box(0);
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
                    leanh::lean_inc(v___x_1008_);
                    v___x_1013_ = l_Lean_Syntax_isOfKind(v___x_1008_, v___x_1012_);
                    if v___x_1013_ == 0 {
                        leanh::lean_dec(v___x_1008_);
                        leanh::lean_dec(v___x_972_);
                        leanh::lean_dec(v_args_x3f_969_);
                        leanh::lean_dec(v___y_968_);
                        leanh::lean_dec(v___y_966_);
                        leanh::lean_dec(v___y_962_);
                        leanh::lean_dec(v___y_960_);
                        v___x_1014_ =
                            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                        v___x_1015_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_x_649_,
                            v___x_1014_,
                            v___y_970_,
                            v___y_971_,
                        );
                        leanh::lean_dec(v_x_649_);
                        return v___x_1015_;
                    } else {
                        v___x_1016_ = l_Lean_Syntax_getArg(v___x_1008_, v___y_964_);
                        leanh::lean_dec(v___x_1008_);
                        v___x_1017_ = l_Lean_Syntax_getArg(v___x_972_, v___y_964_);
                        leanh::lean_dec(v___x_972_);
                        v___x_1018_ = l_Lean_Syntax_isNone(v___x_1017_);
                        if v___x_1018_ == 0 {
                            leanh::lean_inc(v___x_1017_);
                            v___x_1019_ = l_Lean_Syntax_matchesNull(v___x_1017_, v___y_964_);
                            if v___x_1019_ == 0 {
                                leanh::lean_dec(v___x_1017_);
                                leanh::lean_dec(v___x_1016_);
                                leanh::lean_dec(v_args_x3f_969_);
                                leanh::lean_dec(v___y_968_);
                                leanh::lean_dec(v___y_966_);
                                leanh::lean_dec(v___y_962_);
                                leanh::lean_dec(v___y_960_);
                                v___x_1020_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                v___x_1021_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_x_649_,
                                    v___x_1020_,
                                    v___y_970_,
                                    v___y_971_,
                                );
                                leanh::lean_dec(v_x_649_);
                                return v___x_1021_;
                            } else {
                                v_wds_x3f_1022_ = l_Lean_Syntax_getArg(v___x_1017_, v___x_701_);
                                leanh::lean_dec(v___x_1017_);
                                v___x_1023_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51;
                                leanh::lean_inc(v_wds_x3f_1022_);
                                v___x_1024_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1022_, v___x_1023_);
                                if v___x_1024_ == 0 {
                                    leanh::lean_dec(v_wds_x3f_1022_);
                                    leanh::lean_dec(v___x_1016_);
                                    leanh::lean_dec(v_args_x3f_969_);
                                    leanh::lean_dec(v___y_968_);
                                    leanh::lean_dec(v___y_966_);
                                    leanh::lean_dec(v___y_962_);
                                    leanh::lean_dec(v___y_960_);
                                    v___x_1025_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                                    v___x_1026_ = l_Lean_Macro_throwErrorAt___redArg(
                                        v_x_649_,
                                        v___x_1025_,
                                        v___y_970_,
                                        v___y_971_,
                                    );
                                    leanh::lean_dec(v_x_649_);
                                    return v___x_1026_;
                                } else {
                                    leanh::lean_dec(v_x_649_);
                                    v___x_1027_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1027_, 0, v_wds_x3f_1022_);
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
                            leanh::lean_dec(v___x_1017_);
                            leanh::lean_dec(v_x_649_);
                            v___x_1028_ = leanh::lean_box(0);
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
                v___x_1035_ = leanh::lean_unsigned_to_nat(3);
                v___x_1036_ = l_Lean_Syntax_getArg(v_x_649_, v___x_1035_);
                v___x_1037_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55;
                leanh::lean_inc(v___x_1036_);
                v___x_1038_ = l_Lean_Syntax_isOfKind(v___x_1036_, v___x_1037_);
                if v___x_1038_ == 0 {
                    leanh::lean_dec(v___x_1036_);
                    leanh::lean_dec(v_attrs_x3f_1032_);
                    leanh::lean_dec(v___y_1031_);
                    v___x_1039_ =
                        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                    v___x_1040_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_x_649_,
                        v___x_1039_,
                        v___y_1033_,
                        v___y_1034_,
                    );
                    leanh::lean_dec(v_x_649_);
                    return v___x_1040_;
                } else {
                    v___x_1041_ = leanh::lean_unsigned_to_nat(2);
                    v_kw_1042_ = l_Lean_Syntax_getArg(v_x_649_, v___x_1041_);
                    v_name_1043_ = l_Lean_Syntax_getArg(v___x_1036_, v___x_701_);
                    v___x_1044_ = l_Lean_Syntax_getArg(v___x_1036_, v___y_1030_);
                    v___x_1045_ = l_Lean_Syntax_isNone(v___x_1044_);
                    if v___x_1045_ == 0 {
                        leanh::lean_inc(v___x_1044_);
                        v___x_1046_ = l_Lean_Syntax_matchesNull(v___x_1044_, v___y_1030_);
                        if v___x_1046_ == 0 {
                            leanh::lean_dec(v___x_1044_);
                            leanh::lean_dec(v_name_1043_);
                            leanh::lean_dec(v_kw_1042_);
                            leanh::lean_dec(v___x_1036_);
                            leanh::lean_dec(v_attrs_x3f_1032_);
                            leanh::lean_dec(v___y_1031_);
                            v___x_1047_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                            v___x_1048_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_x_649_,
                                v___x_1047_,
                                v___y_1033_,
                                v___y_1034_,
                            );
                            leanh::lean_dec(v_x_649_);
                            return v___x_1048_;
                        } else {
                            v_args_x3f_1049_ = l_Lean_Syntax_getArg(v___x_1044_, v___x_701_);
                            leanh::lean_dec(v___x_1044_);
                            v___x_1050_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1050_, 0, v_args_x3f_1049_);
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
                        leanh::lean_dec(v___x_1044_);
                        v___x_1051_ = leanh::lean_box(0);
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
                v___x_1056_ = leanh::lean_unsigned_to_nat(1);
                v___x_1057_ = l_Lean_Syntax_getArg(v_x_649_, v___x_1056_);
                v___x_1058_ = l_Lean_Syntax_isNone(v___x_1057_);
                if v___x_1058_ == 0 {
                    leanh::lean_inc(v___x_1057_);
                    v___x_1059_ = l_Lean_Syntax_matchesNull(v___x_1057_, v___x_1056_);
                    if v___x_1059_ == 0 {
                        leanh::lean_dec(v___x_1057_);
                        leanh::lean_dec(v_doc_x3f_1053_);
                        v___x_1060_ =
                            l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4;
                        v___x_1061_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_x_649_,
                            v___x_1060_,
                            v___y_1054_,
                            v___y_1055_,
                        );
                        leanh::lean_dec(v_x_649_);
                        return v___x_1061_;
                    } else {
                        v_attrs_x3f_1062_ = l_Lean_Syntax_getArg(v___x_1057_, v___x_701_);
                        leanh::lean_dec(v___x_1057_);
                        v___x_1063_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1063_, 0, v_attrs_x3f_1062_);
                        v___y_1030_ = v___x_1056_;
                        v___y_1031_ = v_doc_x3f_1053_;
                        v_attrs_x3f_1032_ = v___x_1063_;
                        v___y_1033_ = v___y_1054_;
                        v___y_1034_ = v___y_1055_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1057_);
                    v___x_1064_ = leanh::lean_box(0);
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
    mut v_x_1074_: *mut leanh::LeanObject,
    mut v_a_1075_: *mut leanh::LeanObject,
    mut v_a_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1077_ =
        l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl(v_x_1074_, v_a_1075_, v_a_1076_);
    leanh::lean_dec_ref(v_a_1075_);
    return v_res_1077_;
}
pub unsafe fn l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1()
-> *mut leanh::LeanObject {
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = l_Lean_Elab_macroAttribute;
    v___x_1107_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3;
    v___x_1108_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10;
    v___x_1109_ = leanh::lean_alloc_closure(
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
    mut v_a_1111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1112_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
    return v_res_1112_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Script(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Package(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Attributes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Script(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Script(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Package(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_Attributes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Script(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Script(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_Script(builtin);
}
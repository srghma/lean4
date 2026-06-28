// Lean compiler output
// Module: Lean.Elab.Mixfix
// Imports: Lean.Elab.Attributes Init.Syntax
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_Syntax_mkNumLit, l_Lean_evalPrec,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Macro_throwUnsupported___redArg,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node5,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Syntax::{
    initialize_Init_Syntax, l_Lean_Syntax_setArg, runtime_initialize_Init_Syntax,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Attributes::{
    initialize_Lean_Elab_Attributes, l_Lean_Elab_mkAttrKindGlobal,
    runtime_initialize_Lean_Elab_Attributes,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value:
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value:
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 100, 101, 110, 116, 80, 114, 101, 99, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        9101404829963262459 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 114, 103, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value)
            as *mut crate::leanh::LeanObject,
        6287119281958077034 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__8_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__9_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__10_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [108, 104, 115, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__10_value)
            as *mut crate::leanh::LeanObject,
        5328765574789290742 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 104, 115, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value)
            as *mut crate::leanh::LeanObject,
        969147236311963285 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value:
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
    m_data: [109, 105, 120, 102, 105, 120, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value)
            as *mut crate::leanh::LeanObject,
        43679389351681793 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 97, 109, 101, 100, 80, 114, 105, 111, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value)
            as *mut crate::leanh::LeanObject,
        13348752267415789739 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__21_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [112, 114, 105, 111, 114, 105, 116, 121, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__22_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__23_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__24_value:
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__25_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 97, 109, 101, 100, 78, 97, 109, 101, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value)
            as *mut crate::leanh::LeanObject,
        17682753938374962505 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__30_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__31_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [110, 111, 116, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value)
            as *mut crate::leanh::LeanObject,
        13116756686754095629 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__35_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value:
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value)
            as *mut crate::leanh::LeanObject,
        7983999284776576032 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value:
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
    m_data: [105, 110, 102, 105, 120, 108, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value)
            as *mut crate::leanh::LeanObject,
        12494365462036000886 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value:
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
    m_data: [105, 110, 102, 105, 120, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value)
            as *mut crate::leanh::LeanObject,
        10188811159498705416 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value:
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
    m_data: [105, 110, 102, 105, 120, 114, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value)
            as *mut crate::leanh::LeanObject,
        16268699076359030537 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value:
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
    m_data: [112, 114, 101, 102, 105, 120, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value)
            as *mut crate::leanh::LeanObject,
        11805246081692270559 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 111, 115, 116, 102, 105, 120, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value)
            as *mut crate::leanh::LeanObject,
        760317308010147681 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [112, 114, 101, 99, 101, 100, 101, 110, 99, 101, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value)
            as *mut crate::leanh::LeanObject,
        11586196343691998021 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value)
            as *mut crate::leanh::LeanObject,
        2533412339571800130 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value)
            as *mut crate::leanh::LeanObject,
        9063780239635860524 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Command_expandMixfix___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Command_expandMixfix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 112, 97, 110, 100, 77, 105, 120, 102, 105, 120, 0]};
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,16981400742628996529 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value) as *mut crate::leanh::LeanObject,15249639513547833186 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 11 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 44 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 44 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 11 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 11 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 60 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 60 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(
    mut v_stx_1497_: *mut crate::leanh::LeanObject,
    mut v_f_1498_: *mut crate::leanh::LeanObject,
    mut v_a_1499_: *mut crate::leanh::LeanObject,
    mut v_a_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrKind_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1510_: u8 = 0;
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut v_a_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1501_ = crate::leanh::lean_unsigned_to_nat(2);
                v_attrKind_1502_ = l_Lean_Syntax_getArg(v_stx_1497_, v___x_1501_);
                v___x_1503_ = l_Lean_Elab_mkAttrKindGlobal;
                v_stx_1504_ = l_Lean_Syntax_setArg(v_stx_1497_, v___x_1501_, v___x_1503_);
                crate::leanh::lean_inc_ref(v_a_1499_);
                v___x_1505_ =
                    crate::leanh::lean_apply_3(v_f_1498_, v_stx_1504_, v_a_1499_, v_a_1500_);
                if crate::leanh::lean_obj_tag(v___x_1505_) == 0 {
                    v_a_1506_ = crate::leanh::lean_ctor_get(v___x_1505_, 0);
                    v_a_1507_ = crate::leanh::lean_ctor_get(v___x_1505_, 1);
                    v_isSharedCheck_1515_ = (!crate::leanh::lean_is_exclusive(v___x_1505_)) as u8;
                    if v_isSharedCheck_1515_ == 0 {
                        v___x_1509_ = v___x_1505_;
                        v_isShared_1510_ = v_isSharedCheck_1515_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1507_);
                        crate::leanh::lean_inc(v_a_1506_);
                        crate::leanh::lean_dec(v___x_1505_);
                        v___x_1509_ = crate::leanh::lean_box(0);
                        v_isShared_1510_ = v_isSharedCheck_1515_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_attrKind_1502_);
                    v_a_1516_ = crate::leanh::lean_ctor_get(v___x_1505_, 0);
                    v_a_1517_ = crate::leanh::lean_ctor_get(v___x_1505_, 1);
                    v_isSharedCheck_1524_ = (!crate::leanh::lean_is_exclusive(v___x_1505_)) as u8;
                    if v_isSharedCheck_1524_ == 0 {
                        v___x_1519_ = v___x_1505_;
                        v_isShared_1520_ = v_isSharedCheck_1524_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1517_);
                        crate::leanh::lean_inc(v_a_1516_);
                        crate::leanh::lean_dec(v___x_1505_);
                        v___x_1519_ = crate::leanh::lean_box(0);
                        v_isShared_1520_ = v_isSharedCheck_1524_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1511_ = l_Lean_Syntax_setArg(v_a_1506_, v___x_1501_, v_attrKind_1502_);
                if v_isShared_1510_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1509_, 0, v___x_1511_);
                    v___x_1513_ = v___x_1509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_a_1507_);
                    v___x_1513_ = v_reuseFailAlloc_1514_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1513_;
            }
            3 => {
                if v_isShared_1520_ == 0 {
                    v___x_1522_ = v___x_1519_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1523_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1516_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_a_1517_);
                    v___x_1522_ = v_reuseFailAlloc_1523_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal___boxed(
    mut v_stx_1525_: *mut crate::leanh::LeanObject,
    mut v_f_1526_: *mut crate::leanh::LeanObject,
    mut v_a_1527_: *mut crate::leanh::LeanObject,
    mut v_a_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1529_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(
        v_stx_1525_,
        v_f_1526_,
        v_a_1527_,
        v_a_1528_,
    );
    crate::leanh::lean_dec_ref(v_a_1527_);
    return v_res_1529_;
}
pub unsafe fn _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__5;
    v___x_1541_ = l_String_toRawSubstring_x27(v___x_1540_);
    return v___x_1541_;
}
pub unsafe fn _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__10;
    v___x_1548_ = l_String_toRawSubstring_x27(v___x_1547_);
    return v___x_1548_;
}
pub unsafe fn _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__13;
    v___x_1553_ = l_String_toRawSubstring_x27(v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1594_;
}
pub unsafe fn l_Lean_Elab_Command_expandMixfix___lam__0(
    mut v_stx_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: u8 = 0;
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2037_: u8 = 0;
    let mut v___y_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2064_: u8 = 0;
    let mut v___y_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: u8 = 0;
    let mut v___x_2077_: u8 = 0;
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: u8 = 0;
    let mut v___y_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2225_: u8 = 0;
    let mut v___y_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2359_: u8 = 0;
    let mut v___y_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2400_: u8 = 0;
    let mut v___y_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2403_: u8 = 0;
    let mut v___y_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: u8 = 0;
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2544_: u8 = 0;
    let mut v___y_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2581_: u8 = 0;
    let mut v___y_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2587_: u8 = 0;
    let mut v___y_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: u8 = 0;
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: u8 = 0;
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: u8 = 0;
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v___y_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: u8 = 0;
    let mut v___x_2778_: u8 = 0;
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: u8 = 0;
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: u8 = 0;
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: u8 = 0;
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: u8 = 0;
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: u8 = 0;
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: u8 = 0;
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: u8 = 0;
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: u8 = 0;
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: u8 = 0;
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: u8 = 0;
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: u8 = 0;
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: u8 = 0;
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: u8 = 0;
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: u8 = 0;
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: u8 = 0;
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: u8 = 0;
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: u8 = 0;
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: u8 = 0;
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: u8 = 0;
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1651_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__0;
                v___x_1652_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__1;
                v___x_1923_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__17;
                crate::leanh::lean_inc(v_stx_1648_);
                v___x_1924_ = l_Lean_Syntax_isOfKind(v_stx_1648_, v___x_1923_);
                if v___x_1924_ == 0 {
                    crate::leanh::lean_dec(v_stx_1648_);
                    v___x_1925_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1650_);
                    return v___x_1925_;
                } else {
                    v___x_1926_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2922_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_1926_);
                    v___x_2923_ = l_Lean_Syntax_isNone(v___x_2922_);
                    if v___x_2923_ == 0 {
                        v___x_2924_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_2922_);
                        v___x_2925_ = l_Lean_Syntax_matchesNull(v___x_2922_, v___x_2924_);
                        if v___x_2925_ == 0 {
                            crate::leanh::lean_dec(v___x_2922_);
                            crate::leanh::lean_dec(v_stx_1648_);
                            v___x_2926_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1650_);
                            return v___x_2926_;
                        } else {
                            v_doc_x3f_2927_ = l_Lean_Syntax_getArg(v___x_2922_, v___x_1926_);
                            crate::leanh::lean_dec(v___x_2922_);
                            v___x_2928_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__54;
                            crate::leanh::lean_inc(v_doc_x3f_2927_);
                            v___x_2929_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2927_, v___x_2928_);
                            if v___x_2929_ == 0 {
                                crate::leanh::lean_dec(v_doc_x3f_2927_);
                                crate::leanh::lean_dec(v_stx_1648_);
                                v___x_2930_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1650_);
                                return v___x_2930_;
                            } else {
                                v___x_2931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2931_, 0, v_doc_x3f_2927_);
                                v_doc_x3f_2906_ = v___x_2931_;
                                v___y_2907_ = v___y_1649_;
                                v___y_2908_ = v___y_1650_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2922_);
                        v___x_2932_ = crate::leanh::lean_box(0);
                        v_doc_x3f_2906_ = v___x_2932_;
                        v___y_2907_ = v___y_1649_;
                        v___y_2908_ = v___y_1650_;
                        state = 38;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_1668_);
                v___x_1671_ = l_Array_append___redArg(v___y_1668_, v___y_1670_);
                crate::leanh::lean_dec_ref(v___y_1670_);
                crate::leanh::lean_inc_n(v___y_1655_, 3);
                crate::leanh::lean_inc_n(v___y_1654_, 7);
                v___x_1672_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1672_, 0, v___y_1654_);
                crate::leanh::lean_ctor_set(v___x_1672_, 1, v___y_1655_);
                crate::leanh::lean_ctor_set(v___x_1672_, 2, v___x_1671_);
                v___x_1673_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__4;
                v___x_1674_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6,
                );
                v___x_1675_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__7;
                crate::leanh::lean_inc(v___y_1665_);
                crate::leanh::lean_inc(v___y_1656_);
                v___x_1676_ = l_Lean_addMacroScope(v___y_1656_, v___x_1675_, v___y_1665_);
                v___x_1677_ = crate::leanh::lean_box(0);
                v___x_1678_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1678_, 0, v___y_1654_);
                crate::leanh::lean_ctor_set(v___x_1678_, 1, v___x_1674_);
                crate::leanh::lean_ctor_set(v___x_1678_, 2, v___x_1676_);
                crate::leanh::lean_ctor_set(v___x_1678_, 3, v___x_1677_);
                crate::leanh::lean_inc(v___y_1664_);
                crate::leanh::lean_inc_ref(v___x_1678_);
                v___x_1679_ =
                    l_Lean_Syntax_node2(v___y_1654_, v___x_1673_, v___x_1678_, v___y_1664_);
                v___x_1680_ =
                    l_Lean_Syntax_node2(v___y_1654_, v___y_1655_, v___x_1679_, v___y_1660_);
                v___x_1681_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__8;
                v___x_1682_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1682_, 0, v___y_1654_);
                crate::leanh::lean_ctor_set(v___x_1682_, 1, v___x_1681_);
                v___x_1683_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__9;
                crate::leanh::lean_inc_ref(v___y_1657_);
                v___x_1684_ =
                    l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_1657_, v___x_1683_);
                v___x_1685_ = l_Lean_Syntax_node1(v___y_1654_, v___y_1655_, v___x_1678_);
                v___x_1686_ =
                    l_Lean_Syntax_node2(v___y_1654_, v___x_1684_, v___y_1666_, v___x_1685_);
                v___x_1687_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_1688_ = lean_mk_empty_array_with_capacity(v___x_1687_);
                v___x_1689_ = lean_array_push(v___x_1688_, v___y_1662_);
                v___x_1690_ = lean_array_push(v___x_1689_, v___y_1667_);
                v___x_1691_ = lean_array_push(v___x_1690_, v___y_1669_);
                v___x_1692_ = lean_array_push(v___x_1691_, v___y_1659_);
                v___x_1693_ = lean_array_push(v___x_1692_, v___y_1664_);
                v___x_1694_ = lean_array_push(v___x_1693_, v___y_1658_);
                v___x_1695_ = lean_array_push(v___x_1694_, v___x_1672_);
                v___x_1696_ = lean_array_push(v___x_1695_, v___x_1680_);
                v___x_1697_ = lean_array_push(v___x_1696_, v___x_1682_);
                v___x_1698_ = lean_array_push(v___x_1697_, v___x_1686_);
                crate::leanh::lean_inc(v___y_1663_);
                v___x_1699_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1699_, 0, v___y_1654_);
                crate::leanh::lean_ctor_set(v___x_1699_, 1, v___y_1663_);
                crate::leanh::lean_ctor_set(v___x_1699_, 2, v___x_1698_);
                v___x_1700_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1700_, 0, v___x_1699_);
                crate::leanh::lean_ctor_set(v___x_1700_, 1, v___y_1661_);
                return v___x_1700_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_1702_);
                v___x_1719_ = l_Array_append___redArg(v___y_1702_, v___y_1718_);
                crate::leanh::lean_dec_ref(v___y_1718_);
                crate::leanh::lean_inc_n(v___y_1711_, 3);
                crate::leanh::lean_inc_n(v___y_1715_, 7);
                v___x_1720_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1720_, 0, v___y_1715_);
                crate::leanh::lean_ctor_set(v___x_1720_, 1, v___y_1711_);
                crate::leanh::lean_ctor_set(v___x_1720_, 2, v___x_1719_);
                v___x_1721_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__4;
                v___x_1722_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6,
                );
                v___x_1723_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__7;
                crate::leanh::lean_inc(v___y_1712_);
                crate::leanh::lean_inc(v___y_1703_);
                v___x_1724_ = l_Lean_addMacroScope(v___y_1703_, v___x_1723_, v___y_1712_);
                v___x_1725_ = crate::leanh::lean_box(0);
                v___x_1726_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1726_, 0, v___y_1715_);
                crate::leanh::lean_ctor_set(v___x_1726_, 1, v___x_1722_);
                crate::leanh::lean_ctor_set(v___x_1726_, 2, v___x_1724_);
                crate::leanh::lean_ctor_set(v___x_1726_, 3, v___x_1725_);
                crate::leanh::lean_inc(v___y_1707_);
                crate::leanh::lean_inc_ref(v___x_1726_);
                v___x_1727_ =
                    l_Lean_Syntax_node2(v___y_1715_, v___x_1721_, v___x_1726_, v___y_1707_);
                v___x_1728_ =
                    l_Lean_Syntax_node2(v___y_1715_, v___y_1711_, v___y_1704_, v___x_1727_);
                v___x_1729_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__8;
                v___x_1730_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1730_, 0, v___y_1715_);
                crate::leanh::lean_ctor_set(v___x_1730_, 1, v___x_1729_);
                v___x_1731_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__9;
                crate::leanh::lean_inc_ref(v___y_1709_);
                v___x_1732_ =
                    l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_1709_, v___x_1731_);
                v___x_1733_ = l_Lean_Syntax_node1(v___y_1715_, v___y_1711_, v___x_1726_);
                v___x_1734_ =
                    l_Lean_Syntax_node2(v___y_1715_, v___x_1732_, v___y_1706_, v___x_1733_);
                v___x_1735_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_1736_ = lean_mk_empty_array_with_capacity(v___x_1735_);
                v___x_1737_ = lean_array_push(v___x_1736_, v___y_1708_);
                v___x_1738_ = lean_array_push(v___x_1737_, v___y_1710_);
                v___x_1739_ = lean_array_push(v___x_1738_, v___y_1717_);
                v___x_1740_ = lean_array_push(v___x_1739_, v___y_1716_);
                v___x_1741_ = lean_array_push(v___x_1740_, v___y_1707_);
                v___x_1742_ = lean_array_push(v___x_1741_, v___y_1705_);
                v___x_1743_ = lean_array_push(v___x_1742_, v___x_1720_);
                v___x_1744_ = lean_array_push(v___x_1743_, v___x_1728_);
                v___x_1745_ = lean_array_push(v___x_1744_, v___x_1730_);
                v___x_1746_ = lean_array_push(v___x_1745_, v___x_1734_);
                crate::leanh::lean_inc(v___y_1714_);
                v___x_1747_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1747_, 0, v___y_1715_);
                crate::leanh::lean_ctor_set(v___x_1747_, 1, v___y_1714_);
                crate::leanh::lean_ctor_set(v___x_1747_, 2, v___x_1746_);
                v___x_1748_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1748_, 0, v___x_1747_);
                crate::leanh::lean_ctor_set(v___x_1748_, 1, v___y_1713_);
                return v___x_1748_;
            }
            3 => {
                crate::leanh::lean_inc_ref(v___y_1752_);
                v___x_1770_ = l_Array_append___redArg(v___y_1752_, v___y_1769_);
                crate::leanh::lean_dec_ref(v___y_1769_);
                crate::leanh::lean_inc_n(v___y_1751_, 4);
                crate::leanh::lean_inc_n(v___y_1758_, 11);
                v___x_1771_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1771_, 0, v___y_1758_);
                crate::leanh::lean_ctor_set(v___x_1771_, 1, v___y_1751_);
                crate::leanh::lean_ctor_set(v___x_1771_, 2, v___x_1770_);
                v___x_1772_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__4;
                v___x_1773_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11,
                );
                v___x_1774_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__12;
                crate::leanh::lean_inc_n(v___y_1764_, 2);
                crate::leanh::lean_inc_n(v___y_1750_, 2);
                v___x_1775_ = l_Lean_addMacroScope(v___y_1750_, v___x_1774_, v___y_1764_);
                v___x_1776_ = crate::leanh::lean_box(0);
                v___x_1777_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1777_, 0, v___y_1758_);
                crate::leanh::lean_ctor_set(v___x_1777_, 1, v___x_1773_);
                crate::leanh::lean_ctor_set(v___x_1777_, 2, v___x_1775_);
                crate::leanh::lean_ctor_set(v___x_1777_, 3, v___x_1776_);
                crate::leanh::lean_inc(v___y_1756_);
                v___x_1778_ =
                    l_Lean_Syntax_node2(v___y_1758_, v___y_1756_, v___y_1754_, v___y_1765_);
                v___x_1779_ = l_Lean_Syntax_node1(v___y_1758_, v___y_1751_, v___x_1778_);
                crate::leanh::lean_inc_ref(v___x_1777_);
                v___x_1780_ =
                    l_Lean_Syntax_node2(v___y_1758_, v___x_1772_, v___x_1777_, v___x_1779_);
                v___x_1781_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14,
                );
                v___x_1782_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__15;
                v___x_1783_ = l_Lean_addMacroScope(v___y_1750_, v___x_1782_, v___y_1764_);
                v___x_1784_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1784_, 0, v___y_1758_);
                crate::leanh::lean_ctor_set(v___x_1784_, 1, v___x_1781_);
                crate::leanh::lean_ctor_set(v___x_1784_, 2, v___x_1783_);
                crate::leanh::lean_ctor_set(v___x_1784_, 3, v___x_1776_);
                crate::leanh::lean_inc(v___y_1755_);
                crate::leanh::lean_inc_ref(v___x_1784_);
                v___x_1785_ =
                    l_Lean_Syntax_node2(v___y_1758_, v___x_1772_, v___x_1784_, v___y_1755_);
                v___x_1786_ = l_Lean_Syntax_node3(
                    v___y_1758_,
                    v___y_1751_,
                    v___x_1780_,
                    v___y_1768_,
                    v___x_1785_,
                );
                v___x_1787_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__8;
                v___x_1788_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1788_, 0, v___y_1758_);
                crate::leanh::lean_ctor_set(v___x_1788_, 1, v___x_1787_);
                v___x_1789_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__9;
                crate::leanh::lean_inc_ref(v___y_1759_);
                v___x_1790_ =
                    l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_1759_, v___x_1789_);
                v___x_1791_ =
                    l_Lean_Syntax_node2(v___y_1758_, v___y_1751_, v___x_1777_, v___x_1784_);
                v___x_1792_ =
                    l_Lean_Syntax_node2(v___y_1758_, v___x_1790_, v___y_1753_, v___x_1791_);
                v___x_1793_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_1794_ = lean_mk_empty_array_with_capacity(v___x_1793_);
                v___x_1795_ = lean_array_push(v___x_1794_, v___y_1766_);
                v___x_1796_ = lean_array_push(v___x_1795_, v___y_1762_);
                v___x_1797_ = lean_array_push(v___x_1796_, v___y_1763_);
                v___x_1798_ = lean_array_push(v___x_1797_, v___y_1760_);
                v___x_1799_ = lean_array_push(v___x_1798_, v___y_1755_);
                v___x_1800_ = lean_array_push(v___x_1799_, v___y_1761_);
                v___x_1801_ = lean_array_push(v___x_1800_, v___x_1771_);
                v___x_1802_ = lean_array_push(v___x_1801_, v___x_1786_);
                v___x_1803_ = lean_array_push(v___x_1802_, v___x_1788_);
                v___x_1804_ = lean_array_push(v___x_1803_, v___x_1792_);
                crate::leanh::lean_inc(v___y_1757_);
                v___x_1805_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1805_, 0, v___y_1758_);
                crate::leanh::lean_ctor_set(v___x_1805_, 1, v___y_1757_);
                crate::leanh::lean_ctor_set(v___x_1805_, 2, v___x_1804_);
                v___x_1806_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1806_, 0, v___x_1805_);
                crate::leanh::lean_ctor_set(v___x_1806_, 1, v___y_1767_);
                return v___x_1806_;
            }
            4 => {
                crate::leanh::lean_inc_ref(v___y_1826_);
                v___x_1828_ = l_Array_append___redArg(v___y_1826_, v___y_1827_);
                crate::leanh::lean_dec_ref(v___y_1827_);
                crate::leanh::lean_inc_n(v___y_1809_, 4);
                crate::leanh::lean_inc_n(v___y_1813_, 11);
                v___x_1829_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1829_, 0, v___y_1813_);
                crate::leanh::lean_ctor_set(v___x_1829_, 1, v___y_1809_);
                crate::leanh::lean_ctor_set(v___x_1829_, 2, v___x_1828_);
                v___x_1830_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__4;
                v___x_1831_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11,
                );
                v___x_1832_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__12;
                crate::leanh::lean_inc_n(v___y_1821_, 2);
                crate::leanh::lean_inc_n(v___y_1820_, 2);
                v___x_1833_ = l_Lean_addMacroScope(v___y_1820_, v___x_1832_, v___y_1821_);
                v___x_1834_ = crate::leanh::lean_box(0);
                v___x_1835_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1835_, 0, v___y_1813_);
                crate::leanh::lean_ctor_set(v___x_1835_, 1, v___x_1831_);
                crate::leanh::lean_ctor_set(v___x_1835_, 2, v___x_1833_);
                crate::leanh::lean_ctor_set(v___x_1835_, 3, v___x_1834_);
                crate::leanh::lean_inc(v___y_1819_);
                v___x_1836_ =
                    l_Lean_Syntax_node2(v___y_1813_, v___y_1819_, v___y_1808_, v___y_1822_);
                v___x_1837_ = l_Lean_Syntax_node1(v___y_1813_, v___y_1809_, v___x_1836_);
                crate::leanh::lean_inc(v___x_1837_);
                crate::leanh::lean_inc_ref(v___x_1835_);
                v___x_1838_ =
                    l_Lean_Syntax_node2(v___y_1813_, v___x_1830_, v___x_1835_, v___x_1837_);
                v___x_1839_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14,
                );
                v___x_1840_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__15;
                v___x_1841_ = l_Lean_addMacroScope(v___y_1820_, v___x_1840_, v___y_1821_);
                v___x_1842_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1842_, 0, v___y_1813_);
                crate::leanh::lean_ctor_set(v___x_1842_, 1, v___x_1839_);
                crate::leanh::lean_ctor_set(v___x_1842_, 2, v___x_1841_);
                crate::leanh::lean_ctor_set(v___x_1842_, 3, v___x_1834_);
                crate::leanh::lean_inc_ref(v___x_1842_);
                v___x_1843_ =
                    l_Lean_Syntax_node2(v___y_1813_, v___x_1830_, v___x_1842_, v___x_1837_);
                v___x_1844_ = l_Lean_Syntax_node3(
                    v___y_1813_,
                    v___y_1809_,
                    v___x_1838_,
                    v___y_1823_,
                    v___x_1843_,
                );
                v___x_1845_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__8;
                v___x_1846_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1846_, 0, v___y_1813_);
                crate::leanh::lean_ctor_set(v___x_1846_, 1, v___x_1845_);
                v___x_1847_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__9;
                crate::leanh::lean_inc_ref(v___y_1817_);
                v___x_1848_ =
                    l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_1817_, v___x_1847_);
                v___x_1849_ =
                    l_Lean_Syntax_node2(v___y_1813_, v___y_1809_, v___x_1835_, v___x_1842_);
                v___x_1850_ =
                    l_Lean_Syntax_node2(v___y_1813_, v___x_1848_, v___y_1810_, v___x_1849_);
                v___x_1851_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_1852_ = lean_mk_empty_array_with_capacity(v___x_1851_);
                v___x_1853_ = lean_array_push(v___x_1852_, v___y_1818_);
                v___x_1854_ = lean_array_push(v___x_1853_, v___y_1825_);
                v___x_1855_ = lean_array_push(v___x_1854_, v___y_1812_);
                v___x_1856_ = lean_array_push(v___x_1855_, v___y_1815_);
                v___x_1857_ = lean_array_push(v___x_1856_, v___y_1814_);
                v___x_1858_ = lean_array_push(v___x_1857_, v___y_1816_);
                v___x_1859_ = lean_array_push(v___x_1858_, v___x_1829_);
                v___x_1860_ = lean_array_push(v___x_1859_, v___x_1844_);
                v___x_1861_ = lean_array_push(v___x_1860_, v___x_1846_);
                v___x_1862_ = lean_array_push(v___x_1861_, v___x_1850_);
                crate::leanh::lean_inc(v___y_1824_);
                v___x_1863_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1863_, 0, v___y_1813_);
                crate::leanh::lean_ctor_set(v___x_1863_, 1, v___y_1824_);
                crate::leanh::lean_ctor_set(v___x_1863_, 2, v___x_1862_);
                v___x_1864_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1863_);
                crate::leanh::lean_ctor_set(v___x_1864_, 1, v___y_1811_);
                return v___x_1864_;
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_1879_);
                v___x_1886_ = l_Array_append___redArg(v___y_1879_, v___y_1885_);
                crate::leanh::lean_dec_ref(v___y_1885_);
                crate::leanh::lean_inc_n(v___y_1876_, 4);
                crate::leanh::lean_inc_n(v___y_1882_, 11);
                v___x_1887_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1887_, 0, v___y_1882_);
                crate::leanh::lean_ctor_set(v___x_1887_, 1, v___y_1876_);
                crate::leanh::lean_ctor_set(v___x_1887_, 2, v___x_1886_);
                v___x_1888_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__4;
                v___x_1889_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11,
                );
                v___x_1890_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__12;
                crate::leanh::lean_inc_n(v___y_1878_, 2);
                crate::leanh::lean_inc_n(v___y_1884_, 2);
                v___x_1891_ = l_Lean_addMacroScope(v___y_1884_, v___x_1890_, v___y_1878_);
                v___x_1892_ = crate::leanh::lean_box(0);
                v___x_1893_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1893_, 0, v___y_1882_);
                crate::leanh::lean_ctor_set(v___x_1893_, 1, v___x_1889_);
                crate::leanh::lean_ctor_set(v___x_1893_, 2, v___x_1891_);
                crate::leanh::lean_ctor_set(v___x_1893_, 3, v___x_1892_);
                crate::leanh::lean_inc(v___y_1877_);
                crate::leanh::lean_inc_ref(v___x_1893_);
                v___x_1894_ =
                    l_Lean_Syntax_node2(v___y_1882_, v___x_1888_, v___x_1893_, v___y_1877_);
                v___x_1895_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14,
                );
                v___x_1896_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__15;
                v___x_1897_ = l_Lean_addMacroScope(v___y_1884_, v___x_1896_, v___y_1878_);
                v___x_1898_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1898_, 0, v___y_1882_);
                crate::leanh::lean_ctor_set(v___x_1898_, 1, v___x_1895_);
                crate::leanh::lean_ctor_set(v___x_1898_, 2, v___x_1897_);
                crate::leanh::lean_ctor_set(v___x_1898_, 3, v___x_1892_);
                crate::leanh::lean_inc(v___y_1874_);
                v___x_1899_ =
                    l_Lean_Syntax_node2(v___y_1882_, v___y_1874_, v___y_1867_, v___y_1880_);
                v___x_1900_ = l_Lean_Syntax_node1(v___y_1882_, v___y_1876_, v___x_1899_);
                crate::leanh::lean_inc_ref(v___x_1898_);
                v___x_1901_ =
                    l_Lean_Syntax_node2(v___y_1882_, v___x_1888_, v___x_1898_, v___x_1900_);
                v___x_1902_ = l_Lean_Syntax_node3(
                    v___y_1882_,
                    v___y_1876_,
                    v___x_1894_,
                    v___y_1868_,
                    v___x_1901_,
                );
                v___x_1903_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__8;
                v___x_1904_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1904_, 0, v___y_1882_);
                crate::leanh::lean_ctor_set(v___x_1904_, 1, v___x_1903_);
                v___x_1905_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__9;
                crate::leanh::lean_inc_ref(v___y_1875_);
                v___x_1906_ =
                    l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_1875_, v___x_1905_);
                v___x_1907_ =
                    l_Lean_Syntax_node2(v___y_1882_, v___y_1876_, v___x_1893_, v___x_1898_);
                v___x_1908_ =
                    l_Lean_Syntax_node2(v___y_1882_, v___x_1906_, v___y_1869_, v___x_1907_);
                v___x_1909_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_1910_ = lean_mk_empty_array_with_capacity(v___x_1909_);
                v___x_1911_ = lean_array_push(v___x_1910_, v___y_1873_);
                v___x_1912_ = lean_array_push(v___x_1911_, v___y_1883_);
                v___x_1913_ = lean_array_push(v___x_1912_, v___y_1866_);
                v___x_1914_ = lean_array_push(v___x_1913_, v___y_1881_);
                v___x_1915_ = lean_array_push(v___x_1914_, v___y_1877_);
                v___x_1916_ = lean_array_push(v___x_1915_, v___y_1870_);
                v___x_1917_ = lean_array_push(v___x_1916_, v___x_1887_);
                v___x_1918_ = lean_array_push(v___x_1917_, v___x_1902_);
                v___x_1919_ = lean_array_push(v___x_1918_, v___x_1904_);
                v___x_1920_ = lean_array_push(v___x_1919_, v___x_1908_);
                crate::leanh::lean_inc(v___y_1871_);
                v___x_1921_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1921_, 0, v___y_1882_);
                crate::leanh::lean_ctor_set(v___x_1921_, 1, v___y_1871_);
                crate::leanh::lean_ctor_set(v___x_1921_, 2, v___x_1920_);
                v___x_1922_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1922_, 0, v___x_1921_);
                crate::leanh::lean_ctor_set(v___x_1922_, 1, v___y_1872_);
                return v___x_1922_;
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_1942_);
                v___x_1945_ = l_Array_append___redArg(v___y_1942_, v___y_1944_);
                crate::leanh::lean_dec_ref(v___y_1944_);
                crate::leanh::lean_inc(v___y_1929_);
                crate::leanh::lean_inc(v___y_1928_);
                v___x_1946_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1946_, 0, v___y_1928_);
                crate::leanh::lean_ctor_set(v___x_1946_, 1, v___y_1929_);
                crate::leanh::lean_ctor_set(v___x_1946_, 2, v___x_1945_);
                if crate::leanh::lean_obj_tag(v___y_1932_) == 1 {
                    v_val_1947_ = crate::leanh::lean_ctor_get(v___y_1932_, 0);
                    crate::leanh::lean_inc(v_val_1947_);
                    crate::leanh::lean_dec_ref_known(v___y_1932_, 1);
                    v___x_1948_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                    v___x_1949_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    crate::leanh::lean_inc_n(v___y_1928_, 5);
                    v___x_1950_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1950_, 0, v___y_1928_);
                    crate::leanh::lean_ctor_set(v___x_1950_, 1, v___x_1949_);
                    v___x_1951_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__21;
                    v___x_1952_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1952_, 0, v___y_1928_);
                    crate::leanh::lean_ctor_set(v___x_1952_, 1, v___x_1951_);
                    v___x_1953_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_1954_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1954_, 0, v___y_1928_);
                    crate::leanh::lean_ctor_set(v___x_1954_, 1, v___x_1953_);
                    v___x_1955_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_1956_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1956_, 0, v___y_1928_);
                    crate::leanh::lean_ctor_set(v___x_1956_, 1, v___x_1955_);
                    v___x_1957_ = l_Lean_Syntax_node5(
                        v___y_1928_,
                        v___x_1948_,
                        v___x_1950_,
                        v___x_1952_,
                        v___x_1954_,
                        v_val_1947_,
                        v___x_1956_,
                    );
                    v___x_1958_ = l_Array_mkArray1___redArg(v___x_1957_);
                    v___y_1654_ = v___y_1928_;
                    v___y_1655_ = v___y_1929_;
                    v___y_1656_ = v___y_1930_;
                    v___y_1657_ = v___y_1931_;
                    v___y_1658_ = v___x_1946_;
                    v___y_1659_ = v___y_1933_;
                    v___y_1660_ = v___y_1934_;
                    v___y_1661_ = v___y_1935_;
                    v___y_1662_ = v___y_1936_;
                    v___y_1663_ = v___y_1937_;
                    v___y_1664_ = v___y_1938_;
                    v___y_1665_ = v___y_1940_;
                    v___y_1666_ = v___y_1941_;
                    v___y_1667_ = v___y_1939_;
                    v___y_1668_ = v___y_1942_;
                    v___y_1669_ = v___y_1943_;
                    v___y_1670_ = v___x_1958_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1932_);
                    v___x_1959_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1654_ = v___y_1928_;
                    v___y_1655_ = v___y_1929_;
                    v___y_1656_ = v___y_1930_;
                    v___y_1657_ = v___y_1931_;
                    v___y_1658_ = v___x_1946_;
                    v___y_1659_ = v___y_1933_;
                    v___y_1660_ = v___y_1934_;
                    v___y_1661_ = v___y_1935_;
                    v___y_1662_ = v___y_1936_;
                    v___y_1663_ = v___y_1937_;
                    v___y_1664_ = v___y_1938_;
                    v___y_1665_ = v___y_1940_;
                    v___y_1666_ = v___y_1941_;
                    v___y_1667_ = v___y_1939_;
                    v___y_1668_ = v___y_1942_;
                    v___y_1669_ = v___y_1943_;
                    v___y_1670_ = v___x_1959_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref_n(v___y_1975_, 2);
                v___x_1979_ = l_Array_append___redArg(v___y_1975_, v___y_1978_);
                crate::leanh::lean_dec_ref(v___y_1978_);
                crate::leanh::lean_inc_n(v___y_1964_, 3);
                crate::leanh::lean_inc_n(v___y_1962_, 7);
                v___x_1980_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1980_, 0, v___y_1962_);
                crate::leanh::lean_ctor_set(v___x_1980_, 1, v___y_1964_);
                crate::leanh::lean_ctor_set(v___x_1980_, 2, v___x_1979_);
                v___x_1981_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1981_, 0, v___y_1962_);
                crate::leanh::lean_ctor_set(v___x_1981_, 1, v___y_1964_);
                crate::leanh::lean_ctor_set(v___x_1981_, 2, v___y_1975_);
                crate::leanh::lean_inc(v___y_1961_);
                v___x_1982_ = l_Lean_Syntax_node1(v___y_1962_, v___y_1961_, v___x_1981_);
                crate::leanh::lean_inc_ref(v___y_1963_);
                v___x_1983_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1983_, 0, v___y_1962_);
                crate::leanh::lean_ctor_set(v___x_1983_, 1, v___y_1963_);
                v___x_1984_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
                v___x_1985_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1985_, 0, v___y_1962_);
                crate::leanh::lean_ctor_set(v___x_1985_, 1, v___x_1984_);
                crate::leanh::lean_inc(v___y_1976_);
                v___x_1986_ =
                    l_Lean_Syntax_node2(v___y_1962_, v___y_1976_, v___x_1985_, v___y_1977_);
                v___x_1987_ = l_Lean_Syntax_node1(v___y_1962_, v___y_1964_, v___x_1986_);
                if crate::leanh::lean_obj_tag(v___y_1971_) == 1 {
                    v_val_1988_ = crate::leanh::lean_ctor_get(v___y_1971_, 0);
                    crate::leanh::lean_inc(v_val_1988_);
                    crate::leanh::lean_dec_ref_known(v___y_1971_, 1);
                    v___x_1989_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                    v___x_1990_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    crate::leanh::lean_inc_n(v___y_1962_, 5);
                    v___x_1991_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1991_, 0, v___y_1962_);
                    crate::leanh::lean_ctor_set(v___x_1991_, 1, v___x_1990_);
                    v___x_1992_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__28;
                    v___x_1993_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1993_, 0, v___y_1962_);
                    crate::leanh::lean_ctor_set(v___x_1993_, 1, v___x_1992_);
                    v___x_1994_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_1995_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1995_, 0, v___y_1962_);
                    crate::leanh::lean_ctor_set(v___x_1995_, 1, v___x_1994_);
                    v___x_1996_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_1997_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1997_, 0, v___y_1962_);
                    crate::leanh::lean_ctor_set(v___x_1997_, 1, v___x_1996_);
                    v___x_1998_ = l_Lean_Syntax_node5(
                        v___y_1962_,
                        v___x_1989_,
                        v___x_1991_,
                        v___x_1993_,
                        v___x_1995_,
                        v_val_1988_,
                        v___x_1997_,
                    );
                    v___x_1999_ = l_Array_mkArray1___redArg(v___x_1998_);
                    v___y_1928_ = v___y_1962_;
                    v___y_1929_ = v___y_1964_;
                    v___y_1930_ = v___y_1965_;
                    v___y_1931_ = v___y_1966_;
                    v___y_1932_ = v___y_1967_;
                    v___y_1933_ = v___x_1983_;
                    v___y_1934_ = v___y_1968_;
                    v___y_1935_ = v___y_1969_;
                    v___y_1936_ = v___y_1970_;
                    v___y_1937_ = v___y_1972_;
                    v___y_1938_ = v___x_1987_;
                    v___y_1939_ = v___x_1980_;
                    v___y_1940_ = v___y_1974_;
                    v___y_1941_ = v___y_1973_;
                    v___y_1942_ = v___y_1975_;
                    v___y_1943_ = v___x_1982_;
                    v___y_1944_ = v___x_1999_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1971_);
                    v___x_2000_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1928_ = v___y_1962_;
                    v___y_1929_ = v___y_1964_;
                    v___y_1930_ = v___y_1965_;
                    v___y_1931_ = v___y_1966_;
                    v___y_1932_ = v___y_1967_;
                    v___y_1933_ = v___x_1983_;
                    v___y_1934_ = v___y_1968_;
                    v___y_1935_ = v___y_1969_;
                    v___y_1936_ = v___y_1970_;
                    v___y_1937_ = v___y_1972_;
                    v___y_1938_ = v___x_1987_;
                    v___y_1939_ = v___x_1980_;
                    v___y_1940_ = v___y_1974_;
                    v___y_1941_ = v___y_1973_;
                    v___y_1942_ = v___y_1975_;
                    v___y_1943_ = v___x_1982_;
                    v___y_1944_ = v___x_2000_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v___y_2017_);
                v___x_2020_ = l_Array_append___redArg(v___y_2017_, v___y_2019_);
                crate::leanh::lean_dec_ref(v___y_2019_);
                crate::leanh::lean_inc(v___y_2005_);
                crate::leanh::lean_inc(v___y_2003_);
                v___x_2021_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2021_, 0, v___y_2003_);
                crate::leanh::lean_ctor_set(v___x_2021_, 1, v___y_2005_);
                crate::leanh::lean_ctor_set(v___x_2021_, 2, v___x_2020_);
                if crate::leanh::lean_obj_tag(v___y_2006_) == 1 {
                    v_val_2022_ = crate::leanh::lean_ctor_get(v___y_2006_, 0);
                    crate::leanh::lean_inc(v_val_2022_);
                    crate::leanh::lean_dec_ref_known(v___y_2006_, 1);
                    v___x_2023_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__29;
                    crate::leanh::lean_inc_ref(v___y_2008_);
                    v___x_2024_ =
                        l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_2008_, v___x_2023_);
                    v___x_2025_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__30;
                    crate::leanh::lean_inc_n(v___y_2003_, 4);
                    v___x_2026_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2026_, 0, v___y_2003_);
                    crate::leanh::lean_ctor_set(v___x_2026_, 1, v___x_2025_);
                    crate::leanh::lean_inc_ref(v___y_2017_);
                    v___x_2027_ = l_Array_append___redArg(v___y_2017_, v_val_2022_);
                    crate::leanh::lean_dec(v_val_2022_);
                    crate::leanh::lean_inc(v___y_2005_);
                    v___x_2028_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2028_, 0, v___y_2003_);
                    crate::leanh::lean_ctor_set(v___x_2028_, 1, v___y_2005_);
                    crate::leanh::lean_ctor_set(v___x_2028_, 2, v___x_2027_);
                    v___x_2029_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__31;
                    v___x_2030_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2030_, 0, v___y_2003_);
                    crate::leanh::lean_ctor_set(v___x_2030_, 1, v___x_2029_);
                    v___x_2031_ = l_Lean_Syntax_node3(
                        v___y_2003_,
                        v___x_2024_,
                        v___x_2026_,
                        v___x_2028_,
                        v___x_2030_,
                    );
                    v___x_2032_ = l_Array_mkArray1___redArg(v___x_2031_);
                    v___y_1961_ = v___y_2002_;
                    v___y_1962_ = v___y_2003_;
                    v___y_1963_ = v___y_2004_;
                    v___y_1964_ = v___y_2005_;
                    v___y_1965_ = v___y_2007_;
                    v___y_1966_ = v___y_2008_;
                    v___y_1967_ = v___y_2009_;
                    v___y_1968_ = v___y_2010_;
                    v___y_1969_ = v___y_2011_;
                    v___y_1970_ = v___x_2021_;
                    v___y_1971_ = v___y_2012_;
                    v___y_1972_ = v___y_2013_;
                    v___y_1973_ = v___y_2015_;
                    v___y_1974_ = v___y_2014_;
                    v___y_1975_ = v___y_2017_;
                    v___y_1976_ = v___y_2016_;
                    v___y_1977_ = v___y_2018_;
                    v___y_1978_ = v___x_2032_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2006_);
                    v___x_2033_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1961_ = v___y_2002_;
                    v___y_1962_ = v___y_2003_;
                    v___y_1963_ = v___y_2004_;
                    v___y_1964_ = v___y_2005_;
                    v___y_1965_ = v___y_2007_;
                    v___y_1966_ = v___y_2008_;
                    v___y_1967_ = v___y_2009_;
                    v___y_1968_ = v___y_2010_;
                    v___y_1969_ = v___y_2011_;
                    v___y_1970_ = v___x_2021_;
                    v___y_1971_ = v___y_2012_;
                    v___y_1972_ = v___y_2013_;
                    v___y_1973_ = v___y_2015_;
                    v___y_1974_ = v___y_2014_;
                    v___y_1975_ = v___y_2017_;
                    v___y_1976_ = v___y_2016_;
                    v___y_1977_ = v___y_2018_;
                    v___y_1978_ = v___x_2033_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v_quotContext_2046_ = crate::leanh::lean_ctor_get(v___y_2044_, 1);
                v_currMacroScope_2047_ = crate::leanh::lean_ctor_get(v___y_2044_, 2);
                v_ref_2048_ = crate::leanh::lean_ctor_get(v___y_2044_, 5);
                v___x_2049_ = crate::leanh::lean_unsigned_to_nat(7);
                v___x_2050_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2049_);
                v___x_2051_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_2052_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2051_);
                crate::leanh::lean_dec(v_stx_1648_);
                v___x_2053_ = l_Lean_SourceInfo_fromRef(v_ref_2048_, v___y_2037_);
                v___x_2054_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__32;
                v___x_2055_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__33;
                v___x_2056_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__35;
                v___x_2057_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__36),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36,
                );
                if crate::leanh::lean_obj_tag(v___y_2040_) == 1 {
                    v_val_2058_ = crate::leanh::lean_ctor_get(v___y_2040_, 0);
                    crate::leanh::lean_inc(v_val_2058_);
                    crate::leanh::lean_dec_ref_known(v___y_2040_, 1);
                    v___x_2059_ = l_Array_mkArray1___redArg(v_val_2058_);
                    v___y_2002_ = v___y_2035_;
                    v___y_2003_ = v___x_2053_;
                    v___y_2004_ = v___x_2054_;
                    v___y_2005_ = v___x_2056_;
                    v___y_2006_ = v___y_2039_;
                    v___y_2007_ = v_quotContext_2046_;
                    v___y_2008_ = v___y_2041_;
                    v___y_2009_ = v_prio_2043_;
                    v___y_2010_ = v___x_2050_;
                    v___y_2011_ = v___y_2045_;
                    v___y_2012_ = v___y_2036_;
                    v___y_2013_ = v___x_2055_;
                    v___y_2014_ = v_currMacroScope_2047_;
                    v___y_2015_ = v___x_2052_;
                    v___y_2016_ = v___y_2038_;
                    v___y_2017_ = v___x_2057_;
                    v___y_2018_ = v___y_2042_;
                    v___y_2019_ = v___x_2059_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2040_);
                    v___x_2060_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2002_ = v___y_2035_;
                    v___y_2003_ = v___x_2053_;
                    v___y_2004_ = v___x_2054_;
                    v___y_2005_ = v___x_2056_;
                    v___y_2006_ = v___y_2039_;
                    v___y_2007_ = v_quotContext_2046_;
                    v___y_2008_ = v___y_2041_;
                    v___y_2009_ = v_prio_2043_;
                    v___y_2010_ = v___x_2050_;
                    v___y_2011_ = v___y_2045_;
                    v___y_2012_ = v___y_2036_;
                    v___y_2013_ = v___x_2055_;
                    v___y_2014_ = v_currMacroScope_2047_;
                    v___y_2015_ = v___x_2052_;
                    v___y_2016_ = v___y_2038_;
                    v___y_2017_ = v___x_2057_;
                    v___y_2018_ = v___y_2042_;
                    v___y_2019_ = v___x_2060_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_2074_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_2075_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2074_);
                v___x_2076_ = l_Lean_Syntax_isNone(v___x_2075_);
                if v___x_2076_ == 0 {
                    crate::leanh::lean_inc(v___x_2075_);
                    v___x_2077_ = l_Lean_Syntax_matchesNull(v___x_2075_, v___y_2062_);
                    if v___x_2077_ == 0 {
                        crate::leanh::lean_dec(v___x_2075_);
                        crate::leanh::lean_dec(v_name_2071_);
                        crate::leanh::lean_dec(v___y_2070_);
                        crate::leanh::lean_dec(v___y_2068_);
                        crate::leanh::lean_dec(v___y_2065_);
                        crate::leanh::lean_dec(v_stx_1648_);
                        v___x_2078_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2073_);
                        return v___x_2078_;
                    } else {
                        v___x_2079_ = l_Lean_Syntax_getArg(v___x_2075_, v___x_1926_);
                        crate::leanh::lean_dec(v___x_2075_);
                        v___x_2080_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                        crate::leanh::lean_inc(v___x_2079_);
                        v___x_2081_ = l_Lean_Syntax_isOfKind(v___x_2079_, v___x_2080_);
                        if v___x_2081_ == 0 {
                            crate::leanh::lean_dec(v___x_2079_);
                            crate::leanh::lean_dec(v_name_2071_);
                            crate::leanh::lean_dec(v___y_2070_);
                            crate::leanh::lean_dec(v___y_2068_);
                            crate::leanh::lean_dec(v___y_2065_);
                            crate::leanh::lean_dec(v_stx_1648_);
                            v___x_2082_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2073_);
                            return v___x_2082_;
                        } else {
                            v_prio_2083_ = l_Lean_Syntax_getArg(v___x_2079_, v___y_2067_);
                            crate::leanh::lean_dec(v___x_2079_);
                            v___x_2084_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2084_, 0, v_prio_2083_);
                            v___y_2035_ = v___y_2063_;
                            v___y_2036_ = v_name_2071_;
                            v___y_2037_ = v___y_2064_;
                            v___y_2038_ = v___y_2066_;
                            v___y_2039_ = v___y_2065_;
                            v___y_2040_ = v___y_2068_;
                            v___y_2041_ = v___y_2069_;
                            v___y_2042_ = v___y_2070_;
                            v_prio_2043_ = v___x_2084_;
                            v___y_2044_ = v___y_2072_;
                            v___y_2045_ = v___y_2073_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2075_);
                    v___x_2085_ = crate::leanh::lean_box(0);
                    v___y_2035_ = v___y_2063_;
                    v___y_2036_ = v_name_2071_;
                    v___y_2037_ = v___y_2064_;
                    v___y_2038_ = v___y_2066_;
                    v___y_2039_ = v___y_2065_;
                    v___y_2040_ = v___y_2068_;
                    v___y_2041_ = v___y_2069_;
                    v___y_2042_ = v___y_2070_;
                    v_prio_2043_ = v___x_2085_;
                    v___y_2044_ = v___y_2072_;
                    v___y_2045_ = v___y_2073_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref(v___y_2088_);
                v___x_2104_ = l_Array_append___redArg(v___y_2088_, v___y_2103_);
                crate::leanh::lean_dec_ref(v___y_2103_);
                crate::leanh::lean_inc(v___y_2096_);
                crate::leanh::lean_inc(v___y_2098_);
                v___x_2105_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2105_, 0, v___y_2098_);
                crate::leanh::lean_ctor_set(v___x_2105_, 1, v___y_2096_);
                crate::leanh::lean_ctor_set(v___x_2105_, 2, v___x_2104_);
                if crate::leanh::lean_obj_tag(v___y_2087_) == 1 {
                    v_val_2106_ = crate::leanh::lean_ctor_get(v___y_2087_, 0);
                    crate::leanh::lean_inc(v_val_2106_);
                    crate::leanh::lean_dec_ref_known(v___y_2087_, 1);
                    v___x_2107_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                    v___x_2108_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    crate::leanh::lean_inc_n(v___y_2098_, 5);
                    v___x_2109_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2109_, 0, v___y_2098_);
                    crate::leanh::lean_ctor_set(v___x_2109_, 1, v___x_2108_);
                    v___x_2110_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__21;
                    v___x_2111_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2111_, 0, v___y_2098_);
                    crate::leanh::lean_ctor_set(v___x_2111_, 1, v___x_2110_);
                    v___x_2112_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2113_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2113_, 0, v___y_2098_);
                    crate::leanh::lean_ctor_set(v___x_2113_, 1, v___x_2112_);
                    v___x_2114_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2115_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2115_, 0, v___y_2098_);
                    crate::leanh::lean_ctor_set(v___x_2115_, 1, v___x_2114_);
                    v___x_2116_ = l_Lean_Syntax_node5(
                        v___y_2098_,
                        v___x_2107_,
                        v___x_2109_,
                        v___x_2111_,
                        v___x_2113_,
                        v_val_2106_,
                        v___x_2115_,
                    );
                    v___x_2117_ = l_Array_mkArray1___redArg(v___x_2116_);
                    v___y_1702_ = v___y_2088_;
                    v___y_1703_ = v___y_2089_;
                    v___y_1704_ = v___y_2090_;
                    v___y_1705_ = v___x_2105_;
                    v___y_1706_ = v___y_2091_;
                    v___y_1707_ = v___y_2092_;
                    v___y_1708_ = v___y_2093_;
                    v___y_1709_ = v___y_2094_;
                    v___y_1710_ = v___y_2095_;
                    v___y_1711_ = v___y_2096_;
                    v___y_1712_ = v___y_2097_;
                    v___y_1713_ = v___y_2099_;
                    v___y_1714_ = v___y_2100_;
                    v___y_1715_ = v___y_2098_;
                    v___y_1716_ = v___y_2101_;
                    v___y_1717_ = v___y_2102_;
                    v___y_1718_ = v___x_2117_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2087_);
                    v___x_2118_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1702_ = v___y_2088_;
                    v___y_1703_ = v___y_2089_;
                    v___y_1704_ = v___y_2090_;
                    v___y_1705_ = v___x_2105_;
                    v___y_1706_ = v___y_2091_;
                    v___y_1707_ = v___y_2092_;
                    v___y_1708_ = v___y_2093_;
                    v___y_1709_ = v___y_2094_;
                    v___y_1710_ = v___y_2095_;
                    v___y_1711_ = v___y_2096_;
                    v___y_1712_ = v___y_2097_;
                    v___y_1713_ = v___y_2099_;
                    v___y_1714_ = v___y_2100_;
                    v___y_1715_ = v___y_2098_;
                    v___y_1716_ = v___y_2101_;
                    v___y_1717_ = v___y_2102_;
                    v___y_1718_ = v___x_2118_;
                    state = 2;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_inc_ref_n(v___y_2122_, 2);
                v___x_2138_ = l_Array_append___redArg(v___y_2122_, v___y_2137_);
                crate::leanh::lean_dec_ref(v___y_2137_);
                crate::leanh::lean_inc_n(v___y_2130_, 3);
                crate::leanh::lean_inc_n(v___y_2135_, 7);
                v___x_2139_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2139_, 0, v___y_2135_);
                crate::leanh::lean_ctor_set(v___x_2139_, 1, v___y_2130_);
                crate::leanh::lean_ctor_set(v___x_2139_, 2, v___x_2138_);
                v___x_2140_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2140_, 0, v___y_2135_);
                crate::leanh::lean_ctor_set(v___x_2140_, 1, v___y_2130_);
                crate::leanh::lean_ctor_set(v___x_2140_, 2, v___y_2122_);
                crate::leanh::lean_inc(v___y_2121_);
                v___x_2141_ = l_Lean_Syntax_node1(v___y_2135_, v___y_2121_, v___x_2140_);
                crate::leanh::lean_inc_ref(v___y_2127_);
                v___x_2142_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2142_, 0, v___y_2135_);
                crate::leanh::lean_ctor_set(v___x_2142_, 1, v___y_2127_);
                v___x_2143_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
                v___x_2144_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2144_, 0, v___y_2135_);
                crate::leanh::lean_ctor_set(v___x_2144_, 1, v___x_2143_);
                crate::leanh::lean_inc(v___y_2136_);
                v___x_2145_ =
                    l_Lean_Syntax_node2(v___y_2135_, v___y_2136_, v___x_2144_, v___y_2132_);
                v___x_2146_ = l_Lean_Syntax_node1(v___y_2135_, v___y_2130_, v___x_2145_);
                if crate::leanh::lean_obj_tag(v___y_2120_) == 1 {
                    v_val_2147_ = crate::leanh::lean_ctor_get(v___y_2120_, 0);
                    crate::leanh::lean_inc(v_val_2147_);
                    crate::leanh::lean_dec_ref_known(v___y_2120_, 1);
                    v___x_2148_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                    v___x_2149_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    crate::leanh::lean_inc_n(v___y_2135_, 5);
                    v___x_2150_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2150_, 0, v___y_2135_);
                    crate::leanh::lean_ctor_set(v___x_2150_, 1, v___x_2149_);
                    v___x_2151_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__28;
                    v___x_2152_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2152_, 0, v___y_2135_);
                    crate::leanh::lean_ctor_set(v___x_2152_, 1, v___x_2151_);
                    v___x_2153_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2154_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2154_, 0, v___y_2135_);
                    crate::leanh::lean_ctor_set(v___x_2154_, 1, v___x_2153_);
                    v___x_2155_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2156_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2156_, 0, v___y_2135_);
                    crate::leanh::lean_ctor_set(v___x_2156_, 1, v___x_2155_);
                    v___x_2157_ = l_Lean_Syntax_node5(
                        v___y_2135_,
                        v___x_2148_,
                        v___x_2150_,
                        v___x_2152_,
                        v___x_2154_,
                        v_val_2147_,
                        v___x_2156_,
                    );
                    v___x_2158_ = l_Array_mkArray1___redArg(v___x_2157_);
                    v___y_2087_ = v___y_2123_;
                    v___y_2088_ = v___y_2122_;
                    v___y_2089_ = v___y_2124_;
                    v___y_2090_ = v___y_2125_;
                    v___y_2091_ = v___y_2126_;
                    v___y_2092_ = v___x_2146_;
                    v___y_2093_ = v___y_2128_;
                    v___y_2094_ = v___y_2129_;
                    v___y_2095_ = v___x_2139_;
                    v___y_2096_ = v___y_2130_;
                    v___y_2097_ = v___y_2131_;
                    v___y_2098_ = v___y_2135_;
                    v___y_2099_ = v___y_2134_;
                    v___y_2100_ = v___y_2133_;
                    v___y_2101_ = v___x_2142_;
                    v___y_2102_ = v___x_2141_;
                    v___y_2103_ = v___x_2158_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2120_);
                    v___x_2159_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2087_ = v___y_2123_;
                    v___y_2088_ = v___y_2122_;
                    v___y_2089_ = v___y_2124_;
                    v___y_2090_ = v___y_2125_;
                    v___y_2091_ = v___y_2126_;
                    v___y_2092_ = v___x_2146_;
                    v___y_2093_ = v___y_2128_;
                    v___y_2094_ = v___y_2129_;
                    v___y_2095_ = v___x_2139_;
                    v___y_2096_ = v___y_2130_;
                    v___y_2097_ = v___y_2131_;
                    v___y_2098_ = v___y_2135_;
                    v___y_2099_ = v___y_2134_;
                    v___y_2100_ = v___y_2133_;
                    v___y_2101_ = v___x_2142_;
                    v___y_2102_ = v___x_2141_;
                    v___y_2103_ = v___x_2159_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_inc_ref(v___y_2163_);
                v___x_2179_ = l_Array_append___redArg(v___y_2163_, v___y_2178_);
                crate::leanh::lean_dec_ref(v___y_2178_);
                crate::leanh::lean_inc(v___y_2171_);
                crate::leanh::lean_inc(v___y_2176_);
                v___x_2180_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2180_, 0, v___y_2176_);
                crate::leanh::lean_ctor_set(v___x_2180_, 1, v___y_2171_);
                crate::leanh::lean_ctor_set(v___x_2180_, 2, v___x_2179_);
                if crate::leanh::lean_obj_tag(v___y_2167_) == 1 {
                    v_val_2181_ = crate::leanh::lean_ctor_get(v___y_2167_, 0);
                    crate::leanh::lean_inc(v_val_2181_);
                    crate::leanh::lean_dec_ref_known(v___y_2167_, 1);
                    v___x_2182_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__29;
                    crate::leanh::lean_inc_ref(v___y_2170_);
                    v___x_2183_ =
                        l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_2170_, v___x_2182_);
                    v___x_2184_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__30;
                    crate::leanh::lean_inc_n(v___y_2176_, 4);
                    v___x_2185_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2185_, 0, v___y_2176_);
                    crate::leanh::lean_ctor_set(v___x_2185_, 1, v___x_2184_);
                    crate::leanh::lean_inc_ref(v___y_2163_);
                    v___x_2186_ = l_Array_append___redArg(v___y_2163_, v_val_2181_);
                    crate::leanh::lean_dec(v_val_2181_);
                    crate::leanh::lean_inc(v___y_2171_);
                    v___x_2187_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2187_, 0, v___y_2176_);
                    crate::leanh::lean_ctor_set(v___x_2187_, 1, v___y_2171_);
                    crate::leanh::lean_ctor_set(v___x_2187_, 2, v___x_2186_);
                    v___x_2188_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__31;
                    v___x_2189_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2189_, 0, v___y_2176_);
                    crate::leanh::lean_ctor_set(v___x_2189_, 1, v___x_2188_);
                    v___x_2190_ = l_Lean_Syntax_node3(
                        v___y_2176_,
                        v___x_2183_,
                        v___x_2185_,
                        v___x_2187_,
                        v___x_2189_,
                    );
                    v___x_2191_ = l_Array_mkArray1___redArg(v___x_2190_);
                    v___y_2120_ = v___y_2161_;
                    v___y_2121_ = v___y_2162_;
                    v___y_2122_ = v___y_2163_;
                    v___y_2123_ = v___y_2164_;
                    v___y_2124_ = v___y_2165_;
                    v___y_2125_ = v___y_2166_;
                    v___y_2126_ = v___y_2168_;
                    v___y_2127_ = v___y_2169_;
                    v___y_2128_ = v___x_2180_;
                    v___y_2129_ = v___y_2170_;
                    v___y_2130_ = v___y_2171_;
                    v___y_2131_ = v___y_2172_;
                    v___y_2132_ = v___y_2173_;
                    v___y_2133_ = v___y_2175_;
                    v___y_2134_ = v___y_2174_;
                    v___y_2135_ = v___y_2176_;
                    v___y_2136_ = v___y_2177_;
                    v___y_2137_ = v___x_2191_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2167_);
                    v___x_2192_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2120_ = v___y_2161_;
                    v___y_2121_ = v___y_2162_;
                    v___y_2122_ = v___y_2163_;
                    v___y_2123_ = v___y_2164_;
                    v___y_2124_ = v___y_2165_;
                    v___y_2125_ = v___y_2166_;
                    v___y_2126_ = v___y_2168_;
                    v___y_2127_ = v___y_2169_;
                    v___y_2128_ = v___x_2180_;
                    v___y_2129_ = v___y_2170_;
                    v___y_2130_ = v___y_2171_;
                    v___y_2131_ = v___y_2172_;
                    v___y_2132_ = v___y_2173_;
                    v___y_2133_ = v___y_2175_;
                    v___y_2134_ = v___y_2174_;
                    v___y_2135_ = v___y_2176_;
                    v___y_2136_ = v___y_2177_;
                    v___y_2137_ = v___x_2192_;
                    state = 12;
                    continue;
                }
            }
            14 => {
                v_quotContext_2205_ = crate::leanh::lean_ctor_get(v___y_2203_, 1);
                v_currMacroScope_2206_ = crate::leanh::lean_ctor_get(v___y_2203_, 2);
                v_ref_2207_ = crate::leanh::lean_ctor_get(v___y_2203_, 5);
                v___x_2208_ = crate::leanh::lean_unsigned_to_nat(7);
                v___x_2209_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2208_);
                v___x_2210_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_2211_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2210_);
                crate::leanh::lean_dec(v_stx_1648_);
                v___x_2212_ = l_Lean_SourceInfo_fromRef(v_ref_2207_, v___y_2198_);
                v___x_2213_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__32;
                v___x_2214_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__33;
                v___x_2215_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__35;
                v___x_2216_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__36),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36,
                );
                if crate::leanh::lean_obj_tag(v___y_2199_) == 1 {
                    v_val_2217_ = crate::leanh::lean_ctor_get(v___y_2199_, 0);
                    crate::leanh::lean_inc(v_val_2217_);
                    crate::leanh::lean_dec_ref_known(v___y_2199_, 1);
                    v___x_2218_ = l_Array_mkArray1___redArg(v_val_2217_);
                    v___y_2161_ = v___y_2194_;
                    v___y_2162_ = v___y_2195_;
                    v___y_2163_ = v___x_2216_;
                    v___y_2164_ = v_prio_2202_;
                    v___y_2165_ = v_quotContext_2205_;
                    v___y_2166_ = v___x_2209_;
                    v___y_2167_ = v___y_2197_;
                    v___y_2168_ = v___x_2211_;
                    v___y_2169_ = v___x_2213_;
                    v___y_2170_ = v___y_2200_;
                    v___y_2171_ = v___x_2215_;
                    v___y_2172_ = v_currMacroScope_2206_;
                    v___y_2173_ = v___y_2196_;
                    v___y_2174_ = v___y_2204_;
                    v___y_2175_ = v___x_2214_;
                    v___y_2176_ = v___x_2212_;
                    v___y_2177_ = v___y_2201_;
                    v___y_2178_ = v___x_2218_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2199_);
                    v___x_2219_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2161_ = v___y_2194_;
                    v___y_2162_ = v___y_2195_;
                    v___y_2163_ = v___x_2216_;
                    v___y_2164_ = v_prio_2202_;
                    v___y_2165_ = v_quotContext_2205_;
                    v___y_2166_ = v___x_2209_;
                    v___y_2167_ = v___y_2197_;
                    v___y_2168_ = v___x_2211_;
                    v___y_2169_ = v___x_2213_;
                    v___y_2170_ = v___y_2200_;
                    v___y_2171_ = v___x_2215_;
                    v___y_2172_ = v_currMacroScope_2206_;
                    v___y_2173_ = v___y_2196_;
                    v___y_2174_ = v___y_2204_;
                    v___y_2175_ = v___x_2214_;
                    v___y_2176_ = v___x_2212_;
                    v___y_2177_ = v___y_2201_;
                    v___y_2178_ = v___x_2219_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_2233_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_2234_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2233_);
                v___x_2235_ = l_Lean_Syntax_isNone(v___x_2234_);
                if v___x_2235_ == 0 {
                    crate::leanh::lean_inc(v___x_2234_);
                    v___x_2236_ = l_Lean_Syntax_matchesNull(v___x_2234_, v___y_2221_);
                    if v___x_2236_ == 0 {
                        crate::leanh::lean_dec(v___x_2234_);
                        crate::leanh::lean_dec(v_name_2230_);
                        crate::leanh::lean_dec(v___y_2227_);
                        crate::leanh::lean_dec(v___y_2224_);
                        crate::leanh::lean_dec(v___y_2223_);
                        crate::leanh::lean_dec(v_stx_1648_);
                        v___x_2237_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2232_);
                        return v___x_2237_;
                    } else {
                        v___x_2238_ = l_Lean_Syntax_getArg(v___x_2234_, v___x_1926_);
                        crate::leanh::lean_dec(v___x_2234_);
                        v___x_2239_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                        crate::leanh::lean_inc(v___x_2238_);
                        v___x_2240_ = l_Lean_Syntax_isOfKind(v___x_2238_, v___x_2239_);
                        if v___x_2240_ == 0 {
                            crate::leanh::lean_dec(v___x_2238_);
                            crate::leanh::lean_dec(v_name_2230_);
                            crate::leanh::lean_dec(v___y_2227_);
                            crate::leanh::lean_dec(v___y_2224_);
                            crate::leanh::lean_dec(v___y_2223_);
                            crate::leanh::lean_dec(v_stx_1648_);
                            v___x_2241_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2232_);
                            return v___x_2241_;
                        } else {
                            v_prio_2242_ = l_Lean_Syntax_getArg(v___x_2238_, v___y_2226_);
                            crate::leanh::lean_dec(v___x_2238_);
                            v___x_2243_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2243_, 0, v_prio_2242_);
                            v___y_2194_ = v_name_2230_;
                            v___y_2195_ = v___y_2222_;
                            v___y_2196_ = v___y_2223_;
                            v___y_2197_ = v___y_2224_;
                            v___y_2198_ = v___y_2225_;
                            v___y_2199_ = v___y_2227_;
                            v___y_2200_ = v___y_2228_;
                            v___y_2201_ = v___y_2229_;
                            v_prio_2202_ = v___x_2243_;
                            v___y_2203_ = v___y_2231_;
                            v___y_2204_ = v___y_2232_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2234_);
                    v___x_2244_ = crate::leanh::lean_box(0);
                    v___y_2194_ = v_name_2230_;
                    v___y_2195_ = v___y_2222_;
                    v___y_2196_ = v___y_2223_;
                    v___y_2197_ = v___y_2224_;
                    v___y_2198_ = v___y_2225_;
                    v___y_2199_ = v___y_2227_;
                    v___y_2200_ = v___y_2228_;
                    v___y_2201_ = v___y_2229_;
                    v_prio_2202_ = v___x_2244_;
                    v___y_2203_ = v___y_2231_;
                    v___y_2204_ = v___y_2232_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_inc_ref(v___y_2248_);
                v___x_2266_ = l_Array_append___redArg(v___y_2248_, v___y_2265_);
                crate::leanh::lean_dec_ref(v___y_2265_);
                crate::leanh::lean_inc(v___y_2247_);
                crate::leanh::lean_inc(v___y_2254_);
                v___x_2267_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2267_, 0, v___y_2254_);
                crate::leanh::lean_ctor_set(v___x_2267_, 1, v___y_2247_);
                crate::leanh::lean_ctor_set(v___x_2267_, 2, v___x_2266_);
                if crate::leanh::lean_obj_tag(v___y_2249_) == 1 {
                    v_val_2268_ = crate::leanh::lean_ctor_get(v___y_2249_, 0);
                    crate::leanh::lean_inc(v_val_2268_);
                    crate::leanh::lean_dec_ref_known(v___y_2249_, 1);
                    v___x_2269_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                    v___x_2270_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    crate::leanh::lean_inc_n(v___y_2254_, 5);
                    v___x_2271_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2271_, 0, v___y_2254_);
                    crate::leanh::lean_ctor_set(v___x_2271_, 1, v___x_2270_);
                    v___x_2272_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__21;
                    v___x_2273_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2273_, 0, v___y_2254_);
                    crate::leanh::lean_ctor_set(v___x_2273_, 1, v___x_2272_);
                    v___x_2274_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2275_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2275_, 0, v___y_2254_);
                    crate::leanh::lean_ctor_set(v___x_2275_, 1, v___x_2274_);
                    v___x_2276_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2277_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2277_, 0, v___y_2254_);
                    crate::leanh::lean_ctor_set(v___x_2277_, 1, v___x_2276_);
                    v___x_2278_ = l_Lean_Syntax_node5(
                        v___y_2254_,
                        v___x_2269_,
                        v___x_2271_,
                        v___x_2273_,
                        v___x_2275_,
                        v_val_2268_,
                        v___x_2277_,
                    );
                    v___x_2279_ = l_Array_mkArray1___redArg(v___x_2278_);
                    v___y_1750_ = v___y_2246_;
                    v___y_1751_ = v___y_2247_;
                    v___y_1752_ = v___y_2248_;
                    v___y_1753_ = v___y_2250_;
                    v___y_1754_ = v___y_2251_;
                    v___y_1755_ = v___y_2252_;
                    v___y_1756_ = v___y_2253_;
                    v___y_1757_ = v___y_2255_;
                    v___y_1758_ = v___y_2254_;
                    v___y_1759_ = v___y_2256_;
                    v___y_1760_ = v___y_2257_;
                    v___y_1761_ = v___x_2267_;
                    v___y_1762_ = v___y_2258_;
                    v___y_1763_ = v___y_2260_;
                    v___y_1764_ = v___y_2259_;
                    v___y_1765_ = v___y_2262_;
                    v___y_1766_ = v___y_2261_;
                    v___y_1767_ = v___y_2263_;
                    v___y_1768_ = v___y_2264_;
                    v___y_1769_ = v___x_2279_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2249_);
                    v___x_2280_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1750_ = v___y_2246_;
                    v___y_1751_ = v___y_2247_;
                    v___y_1752_ = v___y_2248_;
                    v___y_1753_ = v___y_2250_;
                    v___y_1754_ = v___y_2251_;
                    v___y_1755_ = v___y_2252_;
                    v___y_1756_ = v___y_2253_;
                    v___y_1757_ = v___y_2255_;
                    v___y_1758_ = v___y_2254_;
                    v___y_1759_ = v___y_2256_;
                    v___y_1760_ = v___y_2257_;
                    v___y_1761_ = v___x_2267_;
                    v___y_1762_ = v___y_2258_;
                    v___y_1763_ = v___y_2260_;
                    v___y_1764_ = v___y_2259_;
                    v___y_1765_ = v___y_2262_;
                    v___y_1766_ = v___y_2261_;
                    v___y_1767_ = v___y_2263_;
                    v___y_1768_ = v___y_2264_;
                    v___y_1769_ = v___x_2280_;
                    state = 3;
                    continue;
                }
            }
            17 => {
                crate::leanh::lean_inc_ref_n(v___y_2285_, 2);
                v___x_2301_ = l_Array_append___redArg(v___y_2285_, v___y_2300_);
                crate::leanh::lean_dec_ref(v___y_2300_);
                crate::leanh::lean_inc_n(v___y_2284_, 3);
                crate::leanh::lean_inc_n(v___y_2290_, 7);
                v___x_2302_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2302_, 0, v___y_2290_);
                crate::leanh::lean_ctor_set(v___x_2302_, 1, v___y_2284_);
                crate::leanh::lean_ctor_set(v___x_2302_, 2, v___x_2301_);
                v___x_2303_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2303_, 0, v___y_2290_);
                crate::leanh::lean_ctor_set(v___x_2303_, 1, v___y_2284_);
                crate::leanh::lean_ctor_set(v___x_2303_, 2, v___y_2285_);
                crate::leanh::lean_inc(v___y_2282_);
                v___x_2304_ = l_Lean_Syntax_node1(v___y_2290_, v___y_2282_, v___x_2303_);
                crate::leanh::lean_inc_ref(v___y_2298_);
                v___x_2305_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2305_, 0, v___y_2290_);
                crate::leanh::lean_ctor_set(v___x_2305_, 1, v___y_2298_);
                v___x_2306_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
                v___x_2307_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2307_, 0, v___y_2290_);
                crate::leanh::lean_ctor_set(v___x_2307_, 1, v___x_2306_);
                crate::leanh::lean_inc_ref(v___x_2307_);
                crate::leanh::lean_inc(v___y_2289_);
                v___x_2308_ =
                    l_Lean_Syntax_node2(v___y_2290_, v___y_2289_, v___x_2307_, v___y_2286_);
                v___x_2309_ = l_Lean_Syntax_node1(v___y_2290_, v___y_2284_, v___x_2308_);
                if crate::leanh::lean_obj_tag(v___y_2294_) == 1 {
                    v_val_2310_ = crate::leanh::lean_ctor_get(v___y_2294_, 0);
                    crate::leanh::lean_inc(v_val_2310_);
                    crate::leanh::lean_dec_ref_known(v___y_2294_, 1);
                    v___x_2311_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                    v___x_2312_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    crate::leanh::lean_inc_n(v___y_2290_, 5);
                    v___x_2313_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2313_, 0, v___y_2290_);
                    crate::leanh::lean_ctor_set(v___x_2313_, 1, v___x_2312_);
                    v___x_2314_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__28;
                    v___x_2315_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2315_, 0, v___y_2290_);
                    crate::leanh::lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                    v___x_2316_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2317_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2317_, 0, v___y_2290_);
                    crate::leanh::lean_ctor_set(v___x_2317_, 1, v___x_2316_);
                    v___x_2318_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2319_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2319_, 0, v___y_2290_);
                    crate::leanh::lean_ctor_set(v___x_2319_, 1, v___x_2318_);
                    v___x_2320_ = l_Lean_Syntax_node5(
                        v___y_2290_,
                        v___x_2311_,
                        v___x_2313_,
                        v___x_2315_,
                        v___x_2317_,
                        v_val_2310_,
                        v___x_2319_,
                    );
                    v___x_2321_ = l_Array_mkArray1___redArg(v___x_2320_);
                    v___y_2246_ = v___y_2283_;
                    v___y_2247_ = v___y_2284_;
                    v___y_2248_ = v___y_2285_;
                    v___y_2249_ = v___y_2287_;
                    v___y_2250_ = v___y_2288_;
                    v___y_2251_ = v___x_2307_;
                    v___y_2252_ = v___x_2309_;
                    v___y_2253_ = v___y_2289_;
                    v___y_2254_ = v___y_2290_;
                    v___y_2255_ = v___y_2291_;
                    v___y_2256_ = v___y_2292_;
                    v___y_2257_ = v___x_2305_;
                    v___y_2258_ = v___x_2302_;
                    v___y_2259_ = v___y_2293_;
                    v___y_2260_ = v___x_2304_;
                    v___y_2261_ = v___y_2296_;
                    v___y_2262_ = v___y_2295_;
                    v___y_2263_ = v___y_2297_;
                    v___y_2264_ = v___y_2299_;
                    v___y_2265_ = v___x_2321_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2294_);
                    v___x_2322_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2246_ = v___y_2283_;
                    v___y_2247_ = v___y_2284_;
                    v___y_2248_ = v___y_2285_;
                    v___y_2249_ = v___y_2287_;
                    v___y_2250_ = v___y_2288_;
                    v___y_2251_ = v___x_2307_;
                    v___y_2252_ = v___x_2309_;
                    v___y_2253_ = v___y_2289_;
                    v___y_2254_ = v___y_2290_;
                    v___y_2255_ = v___y_2291_;
                    v___y_2256_ = v___y_2292_;
                    v___y_2257_ = v___x_2305_;
                    v___y_2258_ = v___x_2302_;
                    v___y_2259_ = v___y_2293_;
                    v___y_2260_ = v___x_2304_;
                    v___y_2261_ = v___y_2296_;
                    v___y_2262_ = v___y_2295_;
                    v___y_2263_ = v___y_2297_;
                    v___y_2264_ = v___y_2299_;
                    v___y_2265_ = v___x_2322_;
                    state = 16;
                    continue;
                }
            }
            18 => {
                crate::leanh::lean_inc_ref(v___y_2327_);
                v___x_2343_ = l_Array_append___redArg(v___y_2327_, v___y_2342_);
                crate::leanh::lean_dec_ref(v___y_2342_);
                crate::leanh::lean_inc(v___y_2326_);
                crate::leanh::lean_inc(v___y_2333_);
                v___x_2344_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2344_, 0, v___y_2333_);
                crate::leanh::lean_ctor_set(v___x_2344_, 1, v___y_2326_);
                crate::leanh::lean_ctor_set(v___x_2344_, 2, v___x_2343_);
                if crate::leanh::lean_obj_tag(v___y_2331_) == 1 {
                    v_val_2345_ = crate::leanh::lean_ctor_get(v___y_2331_, 0);
                    crate::leanh::lean_inc(v_val_2345_);
                    crate::leanh::lean_dec_ref_known(v___y_2331_, 1);
                    v___x_2346_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__29;
                    crate::leanh::lean_inc_ref(v___y_2335_);
                    v___x_2347_ =
                        l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_2335_, v___x_2346_);
                    v___x_2348_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__30;
                    crate::leanh::lean_inc_n(v___y_2333_, 4);
                    v___x_2349_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2349_, 0, v___y_2333_);
                    crate::leanh::lean_ctor_set(v___x_2349_, 1, v___x_2348_);
                    crate::leanh::lean_inc_ref(v___y_2327_);
                    v___x_2350_ = l_Array_append___redArg(v___y_2327_, v_val_2345_);
                    crate::leanh::lean_dec(v_val_2345_);
                    crate::leanh::lean_inc(v___y_2326_);
                    v___x_2351_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2351_, 0, v___y_2333_);
                    crate::leanh::lean_ctor_set(v___x_2351_, 1, v___y_2326_);
                    crate::leanh::lean_ctor_set(v___x_2351_, 2, v___x_2350_);
                    v___x_2352_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__31;
                    v___x_2353_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2353_, 0, v___y_2333_);
                    crate::leanh::lean_ctor_set(v___x_2353_, 1, v___x_2352_);
                    v___x_2354_ = l_Lean_Syntax_node3(
                        v___y_2333_,
                        v___x_2347_,
                        v___x_2349_,
                        v___x_2351_,
                        v___x_2353_,
                    );
                    v___x_2355_ = l_Array_mkArray1___redArg(v___x_2354_);
                    v___y_2282_ = v___y_2324_;
                    v___y_2283_ = v___y_2325_;
                    v___y_2284_ = v___y_2326_;
                    v___y_2285_ = v___y_2327_;
                    v___y_2286_ = v___y_2328_;
                    v___y_2287_ = v___y_2329_;
                    v___y_2288_ = v___y_2330_;
                    v___y_2289_ = v___y_2332_;
                    v___y_2290_ = v___y_2333_;
                    v___y_2291_ = v___y_2334_;
                    v___y_2292_ = v___y_2335_;
                    v___y_2293_ = v___y_2336_;
                    v___y_2294_ = v___y_2338_;
                    v___y_2295_ = v___y_2337_;
                    v___y_2296_ = v___x_2344_;
                    v___y_2297_ = v___y_2340_;
                    v___y_2298_ = v___y_2339_;
                    v___y_2299_ = v___y_2341_;
                    v___y_2300_ = v___x_2355_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2331_);
                    v___x_2356_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2282_ = v___y_2324_;
                    v___y_2283_ = v___y_2325_;
                    v___y_2284_ = v___y_2326_;
                    v___y_2285_ = v___y_2327_;
                    v___y_2286_ = v___y_2328_;
                    v___y_2287_ = v___y_2329_;
                    v___y_2288_ = v___y_2330_;
                    v___y_2289_ = v___y_2332_;
                    v___y_2290_ = v___y_2333_;
                    v___y_2291_ = v___y_2334_;
                    v___y_2292_ = v___y_2335_;
                    v___y_2293_ = v___y_2336_;
                    v___y_2294_ = v___y_2338_;
                    v___y_2295_ = v___y_2337_;
                    v___y_2296_ = v___x_2344_;
                    v___y_2297_ = v___y_2340_;
                    v___y_2298_ = v___y_2339_;
                    v___y_2299_ = v___y_2341_;
                    v___y_2300_ = v___x_2356_;
                    state = 17;
                    continue;
                }
            }
            19 => {
                crate::leanh::lean_inc(v___y_2361_);
                v___x_2370_ = l_Lean_evalPrec(v___y_2361_, v___y_2368_, v___y_2369_);
                if crate::leanh::lean_obj_tag(v___x_2370_) == 0 {
                    v_a_2371_ = crate::leanh::lean_ctor_get(v___x_2370_, 0);
                    crate::leanh::lean_inc(v_a_2371_);
                    v_a_2372_ = crate::leanh::lean_ctor_get(v___x_2370_, 1);
                    crate::leanh::lean_inc(v_a_2372_);
                    crate::leanh::lean_dec_ref_known(v___x_2370_, 2);
                    v_quotContext_2373_ = crate::leanh::lean_ctor_get(v___y_2368_, 1);
                    v_currMacroScope_2374_ = crate::leanh::lean_ctor_get(v___y_2368_, 2);
                    v_ref_2375_ = crate::leanh::lean_ctor_get(v___y_2368_, 5);
                    v___x_2376_ = crate::leanh::lean_unsigned_to_nat(7);
                    v___x_2377_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2376_);
                    v___x_2378_ = crate::leanh::lean_unsigned_to_nat(9);
                    v___x_2379_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2378_);
                    crate::leanh::lean_dec(v_stx_1648_);
                    v___x_2380_ = lean_nat_add(v_a_2371_, v___y_2358_);
                    crate::leanh::lean_dec(v_a_2371_);
                    v___x_2381_ = l_Nat_reprFast(v___x_2380_);
                    v___x_2382_ = crate::leanh::lean_box(2);
                    v___x_2383_ = l_Lean_Syntax_mkNumLit(v___x_2381_, v___x_2382_);
                    v___x_2384_ = l_Lean_SourceInfo_fromRef(v_ref_2375_, v___y_2359_);
                    v___x_2385_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__32;
                    v___x_2386_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__33;
                    v___x_2387_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__35;
                    v___x_2388_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once
                        ),
                        _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36,
                    );
                    if crate::leanh::lean_obj_tag(v___y_2364_) == 1 {
                        v_val_2389_ = crate::leanh::lean_ctor_get(v___y_2364_, 0);
                        crate::leanh::lean_inc(v_val_2389_);
                        crate::leanh::lean_dec_ref_known(v___y_2364_, 1);
                        v___x_2390_ = l_Array_mkArray1___redArg(v_val_2389_);
                        v___y_2324_ = v___y_2360_;
                        v___y_2325_ = v_quotContext_2373_;
                        v___y_2326_ = v___x_2387_;
                        v___y_2327_ = v___x_2388_;
                        v___y_2328_ = v___y_2361_;
                        v___y_2329_ = v_prio_2367_;
                        v___y_2330_ = v___x_2379_;
                        v___y_2331_ = v___y_2363_;
                        v___y_2332_ = v___y_2365_;
                        v___y_2333_ = v___x_2384_;
                        v___y_2334_ = v___x_2386_;
                        v___y_2335_ = v___y_2366_;
                        v___y_2336_ = v_currMacroScope_2374_;
                        v___y_2337_ = v___x_2383_;
                        v___y_2338_ = v___y_2362_;
                        v___y_2339_ = v___x_2385_;
                        v___y_2340_ = v_a_2372_;
                        v___y_2341_ = v___x_2377_;
                        v___y_2342_ = v___x_2390_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_2364_);
                        v___x_2391_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                        v___y_2324_ = v___y_2360_;
                        v___y_2325_ = v_quotContext_2373_;
                        v___y_2326_ = v___x_2387_;
                        v___y_2327_ = v___x_2388_;
                        v___y_2328_ = v___y_2361_;
                        v___y_2329_ = v_prio_2367_;
                        v___y_2330_ = v___x_2379_;
                        v___y_2331_ = v___y_2363_;
                        v___y_2332_ = v___y_2365_;
                        v___y_2333_ = v___x_2384_;
                        v___y_2334_ = v___x_2386_;
                        v___y_2335_ = v___y_2366_;
                        v___y_2336_ = v_currMacroScope_2374_;
                        v___y_2337_ = v___x_2383_;
                        v___y_2338_ = v___y_2362_;
                        v___y_2339_ = v___x_2385_;
                        v___y_2340_ = v_a_2372_;
                        v___y_2341_ = v___x_2377_;
                        v___y_2342_ = v___x_2391_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_prio_2367_);
                    crate::leanh::lean_dec(v___y_2364_);
                    crate::leanh::lean_dec(v___y_2363_);
                    crate::leanh::lean_dec(v___y_2362_);
                    crate::leanh::lean_dec(v___y_2361_);
                    crate::leanh::lean_dec(v_stx_1648_);
                    v_a_2392_ = crate::leanh::lean_ctor_get(v___x_2370_, 0);
                    v_a_2393_ = crate::leanh::lean_ctor_get(v___x_2370_, 1);
                    v_isSharedCheck_2400_ = (!crate::leanh::lean_is_exclusive(v___x_2370_)) as u8;
                    if v_isSharedCheck_2400_ == 0 {
                        v___x_2395_ = v___x_2370_;
                        v_isShared_2396_ = v_isSharedCheck_2400_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2393_);
                        crate::leanh::lean_inc(v_a_2392_);
                        crate::leanh::lean_dec(v___x_2370_);
                        v___x_2395_ = crate::leanh::lean_box(0);
                        v_isShared_2396_ = v_isSharedCheck_2400_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_2396_ == 0 {
                    v___x_2398_ = v___x_2395_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2399_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_a_2393_);
                    v___x_2398_ = v_reuseFailAlloc_2399_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2398_;
            }
            22 => {
                v___x_2414_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_2415_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2414_);
                v___x_2416_ = l_Lean_Syntax_isNone(v___x_2415_);
                if v___x_2416_ == 0 {
                    crate::leanh::lean_inc(v___x_2415_);
                    v___x_2417_ = l_Lean_Syntax_matchesNull(v___x_2415_, v___y_2402_);
                    if v___x_2417_ == 0 {
                        crate::leanh::lean_dec(v___x_2415_);
                        crate::leanh::lean_dec(v_name_2411_);
                        crate::leanh::lean_dec(v___y_2409_);
                        crate::leanh::lean_dec(v___y_2406_);
                        crate::leanh::lean_dec(v___y_2405_);
                        crate::leanh::lean_dec(v_stx_1648_);
                        v___x_2418_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2413_);
                        return v___x_2418_;
                    } else {
                        v___x_2419_ = l_Lean_Syntax_getArg(v___x_2415_, v___x_1926_);
                        crate::leanh::lean_dec(v___x_2415_);
                        v___x_2420_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                        crate::leanh::lean_inc(v___x_2419_);
                        v___x_2421_ = l_Lean_Syntax_isOfKind(v___x_2419_, v___x_2420_);
                        if v___x_2421_ == 0 {
                            crate::leanh::lean_dec(v___x_2419_);
                            crate::leanh::lean_dec(v_name_2411_);
                            crate::leanh::lean_dec(v___y_2409_);
                            crate::leanh::lean_dec(v___y_2406_);
                            crate::leanh::lean_dec(v___y_2405_);
                            crate::leanh::lean_dec(v_stx_1648_);
                            v___x_2422_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2413_);
                            return v___x_2422_;
                        } else {
                            v_prio_2423_ = l_Lean_Syntax_getArg(v___x_2419_, v___y_2407_);
                            crate::leanh::lean_dec(v___x_2419_);
                            v___x_2424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2424_, 0, v_prio_2423_);
                            v___y_2358_ = v___y_2402_;
                            v___y_2359_ = v___y_2403_;
                            v___y_2360_ = v___y_2404_;
                            v___y_2361_ = v___y_2405_;
                            v___y_2362_ = v_name_2411_;
                            v___y_2363_ = v___y_2406_;
                            v___y_2364_ = v___y_2409_;
                            v___y_2365_ = v___y_2408_;
                            v___y_2366_ = v___y_2410_;
                            v_prio_2367_ = v___x_2424_;
                            v___y_2368_ = v___y_2412_;
                            v___y_2369_ = v___y_2413_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2415_);
                    v___x_2425_ = crate::leanh::lean_box(0);
                    v___y_2358_ = v___y_2402_;
                    v___y_2359_ = v___y_2403_;
                    v___y_2360_ = v___y_2404_;
                    v___y_2361_ = v___y_2405_;
                    v___y_2362_ = v_name_2411_;
                    v___y_2363_ = v___y_2406_;
                    v___y_2364_ = v___y_2409_;
                    v___y_2365_ = v___y_2408_;
                    v___y_2366_ = v___y_2410_;
                    v_prio_2367_ = v___x_2425_;
                    v___y_2368_ = v___y_2412_;
                    v___y_2369_ = v___y_2413_;
                    state = 19;
                    continue;
                }
            }
            23 => {
                crate::leanh::lean_inc_ref(v___y_2445_);
                v___x_2447_ = l_Array_append___redArg(v___y_2445_, v___y_2446_);
                crate::leanh::lean_dec_ref(v___y_2446_);
                crate::leanh::lean_inc(v___y_2428_);
                crate::leanh::lean_inc(v___y_2432_);
                v___x_2448_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2448_, 0, v___y_2432_);
                crate::leanh::lean_ctor_set(v___x_2448_, 1, v___y_2428_);
                crate::leanh::lean_ctor_set(v___x_2448_, 2, v___x_2447_);
                if crate::leanh::lean_obj_tag(v___y_2442_) == 1 {
                    v_val_2449_ = crate::leanh::lean_ctor_get(v___y_2442_, 0);
                    crate::leanh::lean_inc(v_val_2449_);
                    crate::leanh::lean_dec_ref_known(v___y_2442_, 1);
                    v___x_2450_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                    v___x_2451_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    crate::leanh::lean_inc_n(v___y_2432_, 5);
                    v___x_2452_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2452_, 0, v___y_2432_);
                    crate::leanh::lean_ctor_set(v___x_2452_, 1, v___x_2451_);
                    v___x_2453_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__21;
                    v___x_2454_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2454_, 0, v___y_2432_);
                    crate::leanh::lean_ctor_set(v___x_2454_, 1, v___x_2453_);
                    v___x_2455_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2456_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2456_, 0, v___y_2432_);
                    crate::leanh::lean_ctor_set(v___x_2456_, 1, v___x_2455_);
                    v___x_2457_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2458_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2458_, 0, v___y_2432_);
                    crate::leanh::lean_ctor_set(v___x_2458_, 1, v___x_2457_);
                    v___x_2459_ = l_Lean_Syntax_node5(
                        v___y_2432_,
                        v___x_2450_,
                        v___x_2452_,
                        v___x_2454_,
                        v___x_2456_,
                        v_val_2449_,
                        v___x_2458_,
                    );
                    v___x_2460_ = l_Array_mkArray1___redArg(v___x_2459_);
                    v___y_1808_ = v___y_2427_;
                    v___y_1809_ = v___y_2428_;
                    v___y_1810_ = v___y_2429_;
                    v___y_1811_ = v___y_2430_;
                    v___y_1812_ = v___y_2431_;
                    v___y_1813_ = v___y_2432_;
                    v___y_1814_ = v___y_2433_;
                    v___y_1815_ = v___y_2434_;
                    v___y_1816_ = v___x_2448_;
                    v___y_1817_ = v___y_2435_;
                    v___y_1818_ = v___y_2436_;
                    v___y_1819_ = v___y_2437_;
                    v___y_1820_ = v___y_2438_;
                    v___y_1821_ = v___y_2439_;
                    v___y_1822_ = v___y_2441_;
                    v___y_1823_ = v___y_2440_;
                    v___y_1824_ = v___y_2443_;
                    v___y_1825_ = v___y_2444_;
                    v___y_1826_ = v___y_2445_;
                    v___y_1827_ = v___x_2460_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2442_);
                    v___x_2461_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1808_ = v___y_2427_;
                    v___y_1809_ = v___y_2428_;
                    v___y_1810_ = v___y_2429_;
                    v___y_1811_ = v___y_2430_;
                    v___y_1812_ = v___y_2431_;
                    v___y_1813_ = v___y_2432_;
                    v___y_1814_ = v___y_2433_;
                    v___y_1815_ = v___y_2434_;
                    v___y_1816_ = v___x_2448_;
                    v___y_1817_ = v___y_2435_;
                    v___y_1818_ = v___y_2436_;
                    v___y_1819_ = v___y_2437_;
                    v___y_1820_ = v___y_2438_;
                    v___y_1821_ = v___y_2439_;
                    v___y_1822_ = v___y_2441_;
                    v___y_1823_ = v___y_2440_;
                    v___y_1824_ = v___y_2443_;
                    v___y_1825_ = v___y_2444_;
                    v___y_1826_ = v___y_2445_;
                    v___y_1827_ = v___x_2461_;
                    state = 4;
                    continue;
                }
            }
            24 => {
                crate::leanh::lean_inc_ref_n(v___y_2480_, 2);
                v___x_2482_ = l_Array_append___redArg(v___y_2480_, v___y_2481_);
                crate::leanh::lean_dec_ref(v___y_2481_);
                crate::leanh::lean_inc_n(v___y_2463_, 3);
                crate::leanh::lean_inc_n(v___y_2468_, 7);
                v___x_2483_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2483_, 0, v___y_2468_);
                crate::leanh::lean_ctor_set(v___x_2483_, 1, v___y_2463_);
                crate::leanh::lean_ctor_set(v___x_2483_, 2, v___x_2482_);
                v___x_2484_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2484_, 0, v___y_2468_);
                crate::leanh::lean_ctor_set(v___x_2484_, 1, v___y_2463_);
                crate::leanh::lean_ctor_set(v___x_2484_, 2, v___y_2480_);
                crate::leanh::lean_inc(v___y_2464_);
                v___x_2485_ = l_Lean_Syntax_node1(v___y_2468_, v___y_2464_, v___x_2484_);
                crate::leanh::lean_inc_ref(v___y_2477_);
                v___x_2486_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2486_, 0, v___y_2468_);
                crate::leanh::lean_ctor_set(v___x_2486_, 1, v___y_2477_);
                v___x_2487_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
                v___x_2488_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2488_, 0, v___y_2468_);
                crate::leanh::lean_ctor_set(v___x_2488_, 1, v___x_2487_);
                crate::leanh::lean_inc_ref(v___x_2488_);
                crate::leanh::lean_inc(v___y_2471_);
                v___x_2489_ =
                    l_Lean_Syntax_node2(v___y_2468_, v___y_2471_, v___x_2488_, v___y_2465_);
                v___x_2490_ = l_Lean_Syntax_node1(v___y_2468_, v___y_2463_, v___x_2489_);
                if crate::leanh::lean_obj_tag(v___y_2473_) == 1 {
                    v_val_2491_ = crate::leanh::lean_ctor_get(v___y_2473_, 0);
                    crate::leanh::lean_inc(v_val_2491_);
                    crate::leanh::lean_dec_ref_known(v___y_2473_, 1);
                    v___x_2492_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                    v___x_2493_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    crate::leanh::lean_inc_n(v___y_2468_, 5);
                    v___x_2494_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2494_, 0, v___y_2468_);
                    crate::leanh::lean_ctor_set(v___x_2494_, 1, v___x_2493_);
                    v___x_2495_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__28;
                    v___x_2496_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2496_, 0, v___y_2468_);
                    crate::leanh::lean_ctor_set(v___x_2496_, 1, v___x_2495_);
                    v___x_2497_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2498_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2498_, 0, v___y_2468_);
                    crate::leanh::lean_ctor_set(v___x_2498_, 1, v___x_2497_);
                    v___x_2499_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2500_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2500_, 0, v___y_2468_);
                    crate::leanh::lean_ctor_set(v___x_2500_, 1, v___x_2499_);
                    v___x_2501_ = l_Lean_Syntax_node5(
                        v___y_2468_,
                        v___x_2492_,
                        v___x_2494_,
                        v___x_2496_,
                        v___x_2498_,
                        v_val_2491_,
                        v___x_2500_,
                    );
                    v___x_2502_ = l_Array_mkArray1___redArg(v___x_2501_);
                    v___y_2427_ = v___x_2488_;
                    v___y_2428_ = v___y_2463_;
                    v___y_2429_ = v___y_2466_;
                    v___y_2430_ = v___y_2467_;
                    v___y_2431_ = v___x_2485_;
                    v___y_2432_ = v___y_2468_;
                    v___y_2433_ = v___x_2490_;
                    v___y_2434_ = v___x_2486_;
                    v___y_2435_ = v___y_2469_;
                    v___y_2436_ = v___y_2470_;
                    v___y_2437_ = v___y_2471_;
                    v___y_2438_ = v___y_2472_;
                    v___y_2439_ = v___y_2474_;
                    v___y_2440_ = v___y_2476_;
                    v___y_2441_ = v___y_2475_;
                    v___y_2442_ = v___y_2479_;
                    v___y_2443_ = v___y_2478_;
                    v___y_2444_ = v___x_2483_;
                    v___y_2445_ = v___y_2480_;
                    v___y_2446_ = v___x_2502_;
                    state = 23;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2473_);
                    v___x_2503_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2427_ = v___x_2488_;
                    v___y_2428_ = v___y_2463_;
                    v___y_2429_ = v___y_2466_;
                    v___y_2430_ = v___y_2467_;
                    v___y_2431_ = v___x_2485_;
                    v___y_2432_ = v___y_2468_;
                    v___y_2433_ = v___x_2490_;
                    v___y_2434_ = v___x_2486_;
                    v___y_2435_ = v___y_2469_;
                    v___y_2436_ = v___y_2470_;
                    v___y_2437_ = v___y_2471_;
                    v___y_2438_ = v___y_2472_;
                    v___y_2439_ = v___y_2474_;
                    v___y_2440_ = v___y_2476_;
                    v___y_2441_ = v___y_2475_;
                    v___y_2442_ = v___y_2479_;
                    v___y_2443_ = v___y_2478_;
                    v___y_2444_ = v___x_2483_;
                    v___y_2445_ = v___y_2480_;
                    v___y_2446_ = v___x_2503_;
                    state = 23;
                    continue;
                }
            }
            25 => {
                crate::leanh::lean_inc_ref(v___y_2522_);
                v___x_2524_ = l_Array_append___redArg(v___y_2522_, v___y_2523_);
                crate::leanh::lean_dec_ref(v___y_2523_);
                crate::leanh::lean_inc(v___y_2505_);
                crate::leanh::lean_inc(v___y_2510_);
                v___x_2525_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2525_, 0, v___y_2510_);
                crate::leanh::lean_ctor_set(v___x_2525_, 1, v___y_2505_);
                crate::leanh::lean_ctor_set(v___x_2525_, 2, v___x_2524_);
                if crate::leanh::lean_obj_tag(v___y_2511_) == 1 {
                    v_val_2526_ = crate::leanh::lean_ctor_get(v___y_2511_, 0);
                    crate::leanh::lean_inc(v_val_2526_);
                    crate::leanh::lean_dec_ref_known(v___y_2511_, 1);
                    v___x_2527_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__29;
                    crate::leanh::lean_inc_ref(v___y_2512_);
                    v___x_2528_ =
                        l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_2512_, v___x_2527_);
                    v___x_2529_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__30;
                    crate::leanh::lean_inc_n(v___y_2510_, 4);
                    v___x_2530_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2530_, 0, v___y_2510_);
                    crate::leanh::lean_ctor_set(v___x_2530_, 1, v___x_2529_);
                    crate::leanh::lean_inc_ref(v___y_2522_);
                    v___x_2531_ = l_Array_append___redArg(v___y_2522_, v_val_2526_);
                    crate::leanh::lean_dec(v_val_2526_);
                    crate::leanh::lean_inc(v___y_2505_);
                    v___x_2532_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2532_, 0, v___y_2510_);
                    crate::leanh::lean_ctor_set(v___x_2532_, 1, v___y_2505_);
                    crate::leanh::lean_ctor_set(v___x_2532_, 2, v___x_2531_);
                    v___x_2533_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__31;
                    v___x_2534_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2534_, 0, v___y_2510_);
                    crate::leanh::lean_ctor_set(v___x_2534_, 1, v___x_2533_);
                    v___x_2535_ = l_Lean_Syntax_node3(
                        v___y_2510_,
                        v___x_2528_,
                        v___x_2530_,
                        v___x_2532_,
                        v___x_2534_,
                    );
                    v___x_2536_ = l_Array_mkArray1___redArg(v___x_2535_);
                    v___y_2463_ = v___y_2505_;
                    v___y_2464_ = v___y_2506_;
                    v___y_2465_ = v___y_2507_;
                    v___y_2466_ = v___y_2508_;
                    v___y_2467_ = v___y_2509_;
                    v___y_2468_ = v___y_2510_;
                    v___y_2469_ = v___y_2512_;
                    v___y_2470_ = v___x_2525_;
                    v___y_2471_ = v___y_2513_;
                    v___y_2472_ = v___y_2514_;
                    v___y_2473_ = v___y_2515_;
                    v___y_2474_ = v___y_2516_;
                    v___y_2475_ = v___y_2519_;
                    v___y_2476_ = v___y_2518_;
                    v___y_2477_ = v___y_2517_;
                    v___y_2478_ = v___y_2521_;
                    v___y_2479_ = v___y_2520_;
                    v___y_2480_ = v___y_2522_;
                    v___y_2481_ = v___x_2536_;
                    state = 24;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2511_);
                    v___x_2537_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2463_ = v___y_2505_;
                    v___y_2464_ = v___y_2506_;
                    v___y_2465_ = v___y_2507_;
                    v___y_2466_ = v___y_2508_;
                    v___y_2467_ = v___y_2509_;
                    v___y_2468_ = v___y_2510_;
                    v___y_2469_ = v___y_2512_;
                    v___y_2470_ = v___x_2525_;
                    v___y_2471_ = v___y_2513_;
                    v___y_2472_ = v___y_2514_;
                    v___y_2473_ = v___y_2515_;
                    v___y_2474_ = v___y_2516_;
                    v___y_2475_ = v___y_2519_;
                    v___y_2476_ = v___y_2518_;
                    v___y_2477_ = v___y_2517_;
                    v___y_2478_ = v___y_2521_;
                    v___y_2479_ = v___y_2520_;
                    v___y_2480_ = v___y_2522_;
                    v___y_2481_ = v___x_2537_;
                    state = 24;
                    continue;
                }
            }
            26 => {
                crate::leanh::lean_inc(v___y_2543_);
                v___x_2551_ = l_Lean_evalPrec(v___y_2543_, v___y_2549_, v___y_2550_);
                if crate::leanh::lean_obj_tag(v___x_2551_) == 0 {
                    v_a_2552_ = crate::leanh::lean_ctor_get(v___x_2551_, 0);
                    crate::leanh::lean_inc(v_a_2552_);
                    v_a_2553_ = crate::leanh::lean_ctor_get(v___x_2551_, 1);
                    crate::leanh::lean_inc(v_a_2553_);
                    crate::leanh::lean_dec_ref_known(v___x_2551_, 2);
                    v_quotContext_2554_ = crate::leanh::lean_ctor_get(v___y_2549_, 1);
                    v_currMacroScope_2555_ = crate::leanh::lean_ctor_get(v___y_2549_, 2);
                    v_ref_2556_ = crate::leanh::lean_ctor_get(v___y_2549_, 5);
                    v___x_2557_ = crate::leanh::lean_unsigned_to_nat(7);
                    v___x_2558_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2557_);
                    v___x_2559_ = crate::leanh::lean_unsigned_to_nat(9);
                    v___x_2560_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2559_);
                    crate::leanh::lean_dec(v_stx_1648_);
                    v___x_2561_ = lean_nat_add(v_a_2552_, v___y_2540_);
                    crate::leanh::lean_dec(v_a_2552_);
                    v___x_2562_ = l_Nat_reprFast(v___x_2561_);
                    v___x_2563_ = crate::leanh::lean_box(2);
                    v___x_2564_ = l_Lean_Syntax_mkNumLit(v___x_2562_, v___x_2563_);
                    v___x_2565_ = l_Lean_SourceInfo_fromRef(v_ref_2556_, v___y_2544_);
                    v___x_2566_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__32;
                    v___x_2567_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__33;
                    v___x_2568_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__35;
                    v___x_2569_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once
                        ),
                        _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36,
                    );
                    if crate::leanh::lean_obj_tag(v___y_2546_) == 1 {
                        v_val_2570_ = crate::leanh::lean_ctor_get(v___y_2546_, 0);
                        crate::leanh::lean_inc(v_val_2570_);
                        crate::leanh::lean_dec_ref_known(v___y_2546_, 1);
                        v___x_2571_ = l_Array_mkArray1___redArg(v_val_2570_);
                        v___y_2505_ = v___x_2568_;
                        v___y_2506_ = v___y_2542_;
                        v___y_2507_ = v___y_2543_;
                        v___y_2508_ = v___x_2560_;
                        v___y_2509_ = v_a_2553_;
                        v___y_2510_ = v___x_2565_;
                        v___y_2511_ = v___y_2545_;
                        v___y_2512_ = v___y_2547_;
                        v___y_2513_ = v___y_2539_;
                        v___y_2514_ = v_quotContext_2554_;
                        v___y_2515_ = v___y_2541_;
                        v___y_2516_ = v_currMacroScope_2555_;
                        v___y_2517_ = v___x_2566_;
                        v___y_2518_ = v___x_2558_;
                        v___y_2519_ = v___x_2564_;
                        v___y_2520_ = v_prio_2548_;
                        v___y_2521_ = v___x_2567_;
                        v___y_2522_ = v___x_2569_;
                        v___y_2523_ = v___x_2571_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_2546_);
                        v___x_2572_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                        v___y_2505_ = v___x_2568_;
                        v___y_2506_ = v___y_2542_;
                        v___y_2507_ = v___y_2543_;
                        v___y_2508_ = v___x_2560_;
                        v___y_2509_ = v_a_2553_;
                        v___y_2510_ = v___x_2565_;
                        v___y_2511_ = v___y_2545_;
                        v___y_2512_ = v___y_2547_;
                        v___y_2513_ = v___y_2539_;
                        v___y_2514_ = v_quotContext_2554_;
                        v___y_2515_ = v___y_2541_;
                        v___y_2516_ = v_currMacroScope_2555_;
                        v___y_2517_ = v___x_2566_;
                        v___y_2518_ = v___x_2558_;
                        v___y_2519_ = v___x_2564_;
                        v___y_2520_ = v_prio_2548_;
                        v___y_2521_ = v___x_2567_;
                        v___y_2522_ = v___x_2569_;
                        v___y_2523_ = v___x_2572_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_prio_2548_);
                    crate::leanh::lean_dec(v___y_2546_);
                    crate::leanh::lean_dec(v___y_2545_);
                    crate::leanh::lean_dec(v___y_2543_);
                    crate::leanh::lean_dec(v___y_2541_);
                    crate::leanh::lean_dec(v_stx_1648_);
                    v_a_2573_ = crate::leanh::lean_ctor_get(v___x_2551_, 0);
                    v_a_2574_ = crate::leanh::lean_ctor_get(v___x_2551_, 1);
                    v_isSharedCheck_2581_ = (!crate::leanh::lean_is_exclusive(v___x_2551_)) as u8;
                    if v_isSharedCheck_2581_ == 0 {
                        v___x_2576_ = v___x_2551_;
                        v_isShared_2577_ = v_isSharedCheck_2581_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2574_);
                        crate::leanh::lean_inc(v_a_2573_);
                        crate::leanh::lean_dec(v___x_2551_);
                        v___x_2576_ = crate::leanh::lean_box(0);
                        v_isShared_2577_ = v_isSharedCheck_2581_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2577_ == 0 {
                    v___x_2579_ = v___x_2576_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2580_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_a_2574_);
                    v___x_2579_ = v_reuseFailAlloc_2580_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2579_;
            }
            29 => {
                v___x_2595_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_2596_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2595_);
                v___x_2597_ = l_Lean_Syntax_isNone(v___x_2596_);
                if v___x_2597_ == 0 {
                    crate::leanh::lean_inc(v___x_2596_);
                    v___x_2598_ = l_Lean_Syntax_matchesNull(v___x_2596_, v___y_2583_);
                    if v___x_2598_ == 0 {
                        crate::leanh::lean_dec(v___x_2596_);
                        crate::leanh::lean_dec(v_name_2592_);
                        crate::leanh::lean_dec(v___y_2590_);
                        crate::leanh::lean_dec(v___y_2588_);
                        crate::leanh::lean_dec(v___y_2586_);
                        crate::leanh::lean_dec(v_stx_1648_);
                        v___x_2599_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2594_);
                        return v___x_2599_;
                    } else {
                        v___x_2600_ = l_Lean_Syntax_getArg(v___x_2596_, v___x_1926_);
                        crate::leanh::lean_dec(v___x_2596_);
                        v___x_2601_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                        crate::leanh::lean_inc(v___x_2600_);
                        v___x_2602_ = l_Lean_Syntax_isOfKind(v___x_2600_, v___x_2601_);
                        if v___x_2602_ == 0 {
                            crate::leanh::lean_dec(v___x_2600_);
                            crate::leanh::lean_dec(v_name_2592_);
                            crate::leanh::lean_dec(v___y_2590_);
                            crate::leanh::lean_dec(v___y_2588_);
                            crate::leanh::lean_dec(v___y_2586_);
                            crate::leanh::lean_dec(v_stx_1648_);
                            v___x_2603_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2594_);
                            return v___x_2603_;
                        } else {
                            v_prio_2604_ = l_Lean_Syntax_getArg(v___x_2600_, v___y_2589_);
                            crate::leanh::lean_dec(v___x_2600_);
                            v___x_2605_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2605_, 0, v_prio_2604_);
                            v___y_2539_ = v___y_2584_;
                            v___y_2540_ = v___y_2583_;
                            v___y_2541_ = v_name_2592_;
                            v___y_2542_ = v___y_2585_;
                            v___y_2543_ = v___y_2586_;
                            v___y_2544_ = v___y_2587_;
                            v___y_2545_ = v___y_2588_;
                            v___y_2546_ = v___y_2590_;
                            v___y_2547_ = v___y_2591_;
                            v_prio_2548_ = v___x_2605_;
                            v___y_2549_ = v___y_2593_;
                            v___y_2550_ = v___y_2594_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2596_);
                    v___x_2606_ = crate::leanh::lean_box(0);
                    v___y_2539_ = v___y_2584_;
                    v___y_2540_ = v___y_2583_;
                    v___y_2541_ = v_name_2592_;
                    v___y_2542_ = v___y_2585_;
                    v___y_2543_ = v___y_2586_;
                    v___y_2544_ = v___y_2587_;
                    v___y_2545_ = v___y_2588_;
                    v___y_2546_ = v___y_2590_;
                    v___y_2547_ = v___y_2591_;
                    v_prio_2548_ = v___x_2606_;
                    v___y_2549_ = v___y_2593_;
                    v___y_2550_ = v___y_2594_;
                    state = 26;
                    continue;
                }
            }
            30 => {
                crate::leanh::lean_inc_ref(v___y_2621_);
                v___x_2628_ = l_Array_append___redArg(v___y_2621_, v___y_2627_);
                crate::leanh::lean_dec_ref(v___y_2627_);
                crate::leanh::lean_inc(v___y_2618_);
                crate::leanh::lean_inc(v___y_2624_);
                v___x_2629_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2629_, 0, v___y_2624_);
                crate::leanh::lean_ctor_set(v___x_2629_, 1, v___y_2618_);
                crate::leanh::lean_ctor_set(v___x_2629_, 2, v___x_2628_);
                if crate::leanh::lean_obj_tag(v___y_2612_) == 1 {
                    v_val_2630_ = crate::leanh::lean_ctor_get(v___y_2612_, 0);
                    crate::leanh::lean_inc(v_val_2630_);
                    crate::leanh::lean_dec_ref_known(v___y_2612_, 1);
                    v___x_2631_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                    v___x_2632_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    crate::leanh::lean_inc_n(v___y_2624_, 5);
                    v___x_2633_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2633_, 0, v___y_2624_);
                    crate::leanh::lean_ctor_set(v___x_2633_, 1, v___x_2632_);
                    v___x_2634_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__21;
                    v___x_2635_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2635_, 0, v___y_2624_);
                    crate::leanh::lean_ctor_set(v___x_2635_, 1, v___x_2634_);
                    v___x_2636_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2637_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2637_, 0, v___y_2624_);
                    crate::leanh::lean_ctor_set(v___x_2637_, 1, v___x_2636_);
                    v___x_2638_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2639_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2639_, 0, v___y_2624_);
                    crate::leanh::lean_ctor_set(v___x_2639_, 1, v___x_2638_);
                    v___x_2640_ = l_Lean_Syntax_node5(
                        v___y_2624_,
                        v___x_2631_,
                        v___x_2633_,
                        v___x_2635_,
                        v___x_2637_,
                        v_val_2630_,
                        v___x_2639_,
                    );
                    v___x_2641_ = l_Array_mkArray1___redArg(v___x_2640_);
                    v___y_1866_ = v___y_2608_;
                    v___y_1867_ = v___y_2609_;
                    v___y_1868_ = v___y_2610_;
                    v___y_1869_ = v___y_2611_;
                    v___y_1870_ = v___x_2629_;
                    v___y_1871_ = v___y_2613_;
                    v___y_1872_ = v___y_2614_;
                    v___y_1873_ = v___y_2615_;
                    v___y_1874_ = v___y_2616_;
                    v___y_1875_ = v___y_2617_;
                    v___y_1876_ = v___y_2618_;
                    v___y_1877_ = v___y_2619_;
                    v___y_1878_ = v___y_2620_;
                    v___y_1879_ = v___y_2621_;
                    v___y_1880_ = v___y_2622_;
                    v___y_1881_ = v___y_2623_;
                    v___y_1882_ = v___y_2624_;
                    v___y_1883_ = v___y_2626_;
                    v___y_1884_ = v___y_2625_;
                    v___y_1885_ = v___x_2641_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2612_);
                    v___x_2642_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1866_ = v___y_2608_;
                    v___y_1867_ = v___y_2609_;
                    v___y_1868_ = v___y_2610_;
                    v___y_1869_ = v___y_2611_;
                    v___y_1870_ = v___x_2629_;
                    v___y_1871_ = v___y_2613_;
                    v___y_1872_ = v___y_2614_;
                    v___y_1873_ = v___y_2615_;
                    v___y_1874_ = v___y_2616_;
                    v___y_1875_ = v___y_2617_;
                    v___y_1876_ = v___y_2618_;
                    v___y_1877_ = v___y_2619_;
                    v___y_1878_ = v___y_2620_;
                    v___y_1879_ = v___y_2621_;
                    v___y_1880_ = v___y_2622_;
                    v___y_1881_ = v___y_2623_;
                    v___y_1882_ = v___y_2624_;
                    v___y_1883_ = v___y_2626_;
                    v___y_1884_ = v___y_2625_;
                    v___y_1885_ = v___x_2642_;
                    state = 5;
                    continue;
                }
            }
            31 => {
                crate::leanh::lean_inc_ref_n(v___y_2658_, 2);
                v___x_2663_ = l_Array_append___redArg(v___y_2658_, v___y_2662_);
                crate::leanh::lean_dec_ref(v___y_2662_);
                crate::leanh::lean_inc_n(v___y_2655_, 3);
                crate::leanh::lean_inc_n(v___y_2660_, 7);
                v___x_2664_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2664_, 0, v___y_2660_);
                crate::leanh::lean_ctor_set(v___x_2664_, 1, v___y_2655_);
                crate::leanh::lean_ctor_set(v___x_2664_, 2, v___x_2663_);
                v___x_2665_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2665_, 0, v___y_2660_);
                crate::leanh::lean_ctor_set(v___x_2665_, 1, v___y_2655_);
                crate::leanh::lean_ctor_set(v___x_2665_, 2, v___y_2658_);
                crate::leanh::lean_inc(v___y_2644_);
                v___x_2666_ = l_Lean_Syntax_node1(v___y_2660_, v___y_2644_, v___x_2665_);
                crate::leanh::lean_inc_ref(v___y_2649_);
                v___x_2667_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2667_, 0, v___y_2660_);
                crate::leanh::lean_ctor_set(v___x_2667_, 1, v___y_2649_);
                v___x_2668_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
                v___x_2669_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2669_, 0, v___y_2660_);
                crate::leanh::lean_ctor_set(v___x_2669_, 1, v___x_2668_);
                crate::leanh::lean_inc_ref(v___x_2669_);
                crate::leanh::lean_inc(v___y_2653_);
                v___x_2670_ =
                    l_Lean_Syntax_node2(v___y_2660_, v___y_2653_, v___x_2669_, v___y_2646_);
                v___x_2671_ = l_Lean_Syntax_node1(v___y_2660_, v___y_2655_, v___x_2670_);
                if crate::leanh::lean_obj_tag(v___y_2656_) == 1 {
                    v_val_2672_ = crate::leanh::lean_ctor_get(v___y_2656_, 0);
                    crate::leanh::lean_inc(v_val_2672_);
                    crate::leanh::lean_dec_ref_known(v___y_2656_, 1);
                    v___x_2673_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                    v___x_2674_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    crate::leanh::lean_inc_n(v___y_2660_, 5);
                    v___x_2675_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2675_, 0, v___y_2660_);
                    crate::leanh::lean_ctor_set(v___x_2675_, 1, v___x_2674_);
                    v___x_2676_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__28;
                    v___x_2677_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2677_, 0, v___y_2660_);
                    crate::leanh::lean_ctor_set(v___x_2677_, 1, v___x_2676_);
                    v___x_2678_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2679_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2679_, 0, v___y_2660_);
                    crate::leanh::lean_ctor_set(v___x_2679_, 1, v___x_2678_);
                    v___x_2680_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2681_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2681_, 0, v___y_2660_);
                    crate::leanh::lean_ctor_set(v___x_2681_, 1, v___x_2680_);
                    v___x_2682_ = l_Lean_Syntax_node5(
                        v___y_2660_,
                        v___x_2673_,
                        v___x_2675_,
                        v___x_2677_,
                        v___x_2679_,
                        v_val_2672_,
                        v___x_2681_,
                    );
                    v___x_2683_ = l_Array_mkArray1___redArg(v___x_2682_);
                    v___y_2608_ = v___x_2666_;
                    v___y_2609_ = v___x_2669_;
                    v___y_2610_ = v___y_2645_;
                    v___y_2611_ = v___y_2647_;
                    v___y_2612_ = v___y_2648_;
                    v___y_2613_ = v___y_2650_;
                    v___y_2614_ = v___y_2651_;
                    v___y_2615_ = v___y_2652_;
                    v___y_2616_ = v___y_2653_;
                    v___y_2617_ = v___y_2654_;
                    v___y_2618_ = v___y_2655_;
                    v___y_2619_ = v___x_2671_;
                    v___y_2620_ = v___y_2657_;
                    v___y_2621_ = v___y_2658_;
                    v___y_2622_ = v___y_2659_;
                    v___y_2623_ = v___x_2667_;
                    v___y_2624_ = v___y_2660_;
                    v___y_2625_ = v___y_2661_;
                    v___y_2626_ = v___x_2664_;
                    v___y_2627_ = v___x_2683_;
                    state = 30;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2656_);
                    v___x_2684_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2608_ = v___x_2666_;
                    v___y_2609_ = v___x_2669_;
                    v___y_2610_ = v___y_2645_;
                    v___y_2611_ = v___y_2647_;
                    v___y_2612_ = v___y_2648_;
                    v___y_2613_ = v___y_2650_;
                    v___y_2614_ = v___y_2651_;
                    v___y_2615_ = v___y_2652_;
                    v___y_2616_ = v___y_2653_;
                    v___y_2617_ = v___y_2654_;
                    v___y_2618_ = v___y_2655_;
                    v___y_2619_ = v___x_2671_;
                    v___y_2620_ = v___y_2657_;
                    v___y_2621_ = v___y_2658_;
                    v___y_2622_ = v___y_2659_;
                    v___y_2623_ = v___x_2667_;
                    v___y_2624_ = v___y_2660_;
                    v___y_2625_ = v___y_2661_;
                    v___y_2626_ = v___x_2664_;
                    v___y_2627_ = v___x_2684_;
                    state = 30;
                    continue;
                }
            }
            32 => {
                crate::leanh::lean_inc_ref(v___y_2700_);
                v___x_2705_ = l_Array_append___redArg(v___y_2700_, v___y_2704_);
                crate::leanh::lean_dec_ref(v___y_2704_);
                crate::leanh::lean_inc(v___y_2697_);
                crate::leanh::lean_inc(v___y_2702_);
                v___x_2706_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2706_, 0, v___y_2702_);
                crate::leanh::lean_ctor_set(v___x_2706_, 1, v___y_2697_);
                crate::leanh::lean_ctor_set(v___x_2706_, 2, v___x_2705_);
                if crate::leanh::lean_obj_tag(v___y_2694_) == 1 {
                    v_val_2707_ = crate::leanh::lean_ctor_get(v___y_2694_, 0);
                    crate::leanh::lean_inc(v_val_2707_);
                    crate::leanh::lean_dec_ref_known(v___y_2694_, 1);
                    v___x_2708_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__29;
                    crate::leanh::lean_inc_ref(v___y_2696_);
                    v___x_2709_ =
                        l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_2696_, v___x_2708_);
                    v___x_2710_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__30;
                    crate::leanh::lean_inc_n(v___y_2702_, 4);
                    v___x_2711_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2711_, 0, v___y_2702_);
                    crate::leanh::lean_ctor_set(v___x_2711_, 1, v___x_2710_);
                    crate::leanh::lean_inc_ref(v___y_2700_);
                    v___x_2712_ = l_Array_append___redArg(v___y_2700_, v_val_2707_);
                    crate::leanh::lean_dec(v_val_2707_);
                    crate::leanh::lean_inc(v___y_2697_);
                    v___x_2713_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2713_, 0, v___y_2702_);
                    crate::leanh::lean_ctor_set(v___x_2713_, 1, v___y_2697_);
                    crate::leanh::lean_ctor_set(v___x_2713_, 2, v___x_2712_);
                    v___x_2714_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__31;
                    v___x_2715_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2715_, 0, v___y_2702_);
                    crate::leanh::lean_ctor_set(v___x_2715_, 1, v___x_2714_);
                    v___x_2716_ = l_Lean_Syntax_node3(
                        v___y_2702_,
                        v___x_2709_,
                        v___x_2711_,
                        v___x_2713_,
                        v___x_2715_,
                    );
                    v___x_2717_ = l_Array_mkArray1___redArg(v___x_2716_);
                    v___y_2644_ = v___y_2686_;
                    v___y_2645_ = v___y_2687_;
                    v___y_2646_ = v___y_2688_;
                    v___y_2647_ = v___y_2689_;
                    v___y_2648_ = v___y_2690_;
                    v___y_2649_ = v___y_2691_;
                    v___y_2650_ = v___y_2692_;
                    v___y_2651_ = v___y_2693_;
                    v___y_2652_ = v___x_2706_;
                    v___y_2653_ = v___y_2695_;
                    v___y_2654_ = v___y_2696_;
                    v___y_2655_ = v___y_2697_;
                    v___y_2656_ = v___y_2699_;
                    v___y_2657_ = v___y_2698_;
                    v___y_2658_ = v___y_2700_;
                    v___y_2659_ = v___y_2701_;
                    v___y_2660_ = v___y_2702_;
                    v___y_2661_ = v___y_2703_;
                    v___y_2662_ = v___x_2717_;
                    state = 31;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2694_);
                    v___x_2718_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2644_ = v___y_2686_;
                    v___y_2645_ = v___y_2687_;
                    v___y_2646_ = v___y_2688_;
                    v___y_2647_ = v___y_2689_;
                    v___y_2648_ = v___y_2690_;
                    v___y_2649_ = v___y_2691_;
                    v___y_2650_ = v___y_2692_;
                    v___y_2651_ = v___y_2693_;
                    v___y_2652_ = v___x_2706_;
                    v___y_2653_ = v___y_2695_;
                    v___y_2654_ = v___y_2696_;
                    v___y_2655_ = v___y_2697_;
                    v___y_2656_ = v___y_2699_;
                    v___y_2657_ = v___y_2698_;
                    v___y_2658_ = v___y_2700_;
                    v___y_2659_ = v___y_2701_;
                    v___y_2660_ = v___y_2702_;
                    v___y_2661_ = v___y_2703_;
                    v___y_2662_ = v___x_2718_;
                    state = 31;
                    continue;
                }
            }
            33 => {
                crate::leanh::lean_inc(v___y_2723_);
                v___x_2731_ = l_Lean_evalPrec(v___y_2723_, v___y_2729_, v___y_2730_);
                if crate::leanh::lean_obj_tag(v___x_2731_) == 0 {
                    v_a_2732_ = crate::leanh::lean_ctor_get(v___x_2731_, 0);
                    crate::leanh::lean_inc(v_a_2732_);
                    v_a_2733_ = crate::leanh::lean_ctor_get(v___x_2731_, 1);
                    crate::leanh::lean_inc(v_a_2733_);
                    crate::leanh::lean_dec_ref_known(v___x_2731_, 2);
                    v_quotContext_2734_ = crate::leanh::lean_ctor_get(v___y_2729_, 1);
                    v_currMacroScope_2735_ = crate::leanh::lean_ctor_get(v___y_2729_, 2);
                    v_ref_2736_ = crate::leanh::lean_ctor_get(v___y_2729_, 5);
                    v___x_2737_ = crate::leanh::lean_unsigned_to_nat(7);
                    v___x_2738_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2737_);
                    v___x_2739_ = crate::leanh::lean_unsigned_to_nat(9);
                    v___x_2740_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2739_);
                    crate::leanh::lean_dec(v_stx_1648_);
                    v___x_2741_ = lean_nat_add(v_a_2732_, v___y_2721_);
                    crate::leanh::lean_dec(v_a_2732_);
                    v___x_2742_ = l_Nat_reprFast(v___x_2741_);
                    v___x_2743_ = crate::leanh::lean_box(2);
                    v___x_2744_ = l_Lean_Syntax_mkNumLit(v___x_2742_, v___x_2743_);
                    v___x_2745_ = 0;
                    v___x_2746_ = l_Lean_SourceInfo_fromRef(v_ref_2736_, v___x_2745_);
                    v___x_2747_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__32;
                    v___x_2748_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__33;
                    v___x_2749_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__35;
                    v___x_2750_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once
                        ),
                        _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36,
                    );
                    if crate::leanh::lean_obj_tag(v___y_2725_) == 1 {
                        v_val_2751_ = crate::leanh::lean_ctor_get(v___y_2725_, 0);
                        crate::leanh::lean_inc(v_val_2751_);
                        crate::leanh::lean_dec_ref_known(v___y_2725_, 1);
                        v___x_2752_ = l_Array_mkArray1___redArg(v_val_2751_);
                        v___y_2686_ = v___y_2722_;
                        v___y_2687_ = v___x_2738_;
                        v___y_2688_ = v___y_2723_;
                        v___y_2689_ = v___x_2740_;
                        v___y_2690_ = v_prio_2728_;
                        v___y_2691_ = v___x_2747_;
                        v___y_2692_ = v___x_2748_;
                        v___y_2693_ = v_a_2733_;
                        v___y_2694_ = v___y_2724_;
                        v___y_2695_ = v___y_2726_;
                        v___y_2696_ = v___y_2727_;
                        v___y_2697_ = v___x_2749_;
                        v___y_2698_ = v_currMacroScope_2735_;
                        v___y_2699_ = v___y_2720_;
                        v___y_2700_ = v___x_2750_;
                        v___y_2701_ = v___x_2744_;
                        v___y_2702_ = v___x_2746_;
                        v___y_2703_ = v_quotContext_2734_;
                        v___y_2704_ = v___x_2752_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_2725_);
                        v___x_2753_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                        v___y_2686_ = v___y_2722_;
                        v___y_2687_ = v___x_2738_;
                        v___y_2688_ = v___y_2723_;
                        v___y_2689_ = v___x_2740_;
                        v___y_2690_ = v_prio_2728_;
                        v___y_2691_ = v___x_2747_;
                        v___y_2692_ = v___x_2748_;
                        v___y_2693_ = v_a_2733_;
                        v___y_2694_ = v___y_2724_;
                        v___y_2695_ = v___y_2726_;
                        v___y_2696_ = v___y_2727_;
                        v___y_2697_ = v___x_2749_;
                        v___y_2698_ = v_currMacroScope_2735_;
                        v___y_2699_ = v___y_2720_;
                        v___y_2700_ = v___x_2750_;
                        v___y_2701_ = v___x_2744_;
                        v___y_2702_ = v___x_2746_;
                        v___y_2703_ = v_quotContext_2734_;
                        v___y_2704_ = v___x_2753_;
                        state = 32;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_prio_2728_);
                    crate::leanh::lean_dec(v___y_2725_);
                    crate::leanh::lean_dec(v___y_2724_);
                    crate::leanh::lean_dec(v___y_2723_);
                    crate::leanh::lean_dec(v___y_2720_);
                    crate::leanh::lean_dec(v_stx_1648_);
                    v_a_2754_ = crate::leanh::lean_ctor_get(v___x_2731_, 0);
                    v_a_2755_ = crate::leanh::lean_ctor_get(v___x_2731_, 1);
                    v_isSharedCheck_2762_ = (!crate::leanh::lean_is_exclusive(v___x_2731_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v___x_2757_ = v___x_2731_;
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2755_);
                        crate::leanh::lean_inc(v_a_2754_);
                        crate::leanh::lean_dec(v___x_2731_);
                        v___x_2757_ = crate::leanh::lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 34;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_2758_ == 0 {
                    v___x_2760_ = v___x_2757_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2761_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_a_2755_);
                    v___x_2760_ = v_reuseFailAlloc_2761_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2760_;
            }
            36 => {
                v___x_2775_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_2776_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2775_);
                v___x_2777_ = l_Lean_Syntax_isNone(v___x_2776_);
                if v___x_2777_ == 0 {
                    crate::leanh::lean_inc(v___x_2776_);
                    v___x_2778_ = l_Lean_Syntax_matchesNull(v___x_2776_, v___y_2764_);
                    if v___x_2778_ == 0 {
                        crate::leanh::lean_dec(v___x_2776_);
                        crate::leanh::lean_dec(v_name_2772_);
                        crate::leanh::lean_dec(v___y_2770_);
                        crate::leanh::lean_dec(v___y_2767_);
                        crate::leanh::lean_dec(v___y_2766_);
                        crate::leanh::lean_dec(v_stx_1648_);
                        v___x_2779_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2774_);
                        return v___x_2779_;
                    } else {
                        v___x_2780_ = l_Lean_Syntax_getArg(v___x_2776_, v___x_1926_);
                        crate::leanh::lean_dec(v___x_2776_);
                        v___x_2781_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                        crate::leanh::lean_inc(v___x_2780_);
                        v___x_2782_ = l_Lean_Syntax_isOfKind(v___x_2780_, v___x_2781_);
                        if v___x_2782_ == 0 {
                            crate::leanh::lean_dec(v___x_2780_);
                            crate::leanh::lean_dec(v_name_2772_);
                            crate::leanh::lean_dec(v___y_2770_);
                            crate::leanh::lean_dec(v___y_2767_);
                            crate::leanh::lean_dec(v___y_2766_);
                            crate::leanh::lean_dec(v_stx_1648_);
                            v___x_2783_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2774_);
                            return v___x_2783_;
                        } else {
                            v_prio_2784_ = l_Lean_Syntax_getArg(v___x_2780_, v___y_2768_);
                            crate::leanh::lean_dec(v___x_2780_);
                            v___x_2785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2785_, 0, v_prio_2784_);
                            v___y_2720_ = v_name_2772_;
                            v___y_2721_ = v___y_2764_;
                            v___y_2722_ = v___y_2765_;
                            v___y_2723_ = v___y_2766_;
                            v___y_2724_ = v___y_2767_;
                            v___y_2725_ = v___y_2770_;
                            v___y_2726_ = v___y_2769_;
                            v___y_2727_ = v___y_2771_;
                            v_prio_2728_ = v___x_2785_;
                            v___y_2729_ = v___y_2773_;
                            v___y_2730_ = v___y_2774_;
                            state = 33;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2776_);
                    v___x_2786_ = crate::leanh::lean_box(0);
                    v___y_2720_ = v_name_2772_;
                    v___y_2721_ = v___y_2764_;
                    v___y_2722_ = v___y_2765_;
                    v___y_2723_ = v___y_2766_;
                    v___y_2724_ = v___y_2767_;
                    v___y_2725_ = v___y_2770_;
                    v___y_2726_ = v___y_2769_;
                    v___y_2727_ = v___y_2771_;
                    v_prio_2728_ = v___x_2786_;
                    v___y_2729_ = v___y_2773_;
                    v___y_2730_ = v___y_2774_;
                    state = 33;
                    continue;
                }
            }
            37 => {
                v___x_2793_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2794_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2793_);
                v___x_2795_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__37;
                v___x_2796_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__39;
                crate::leanh::lean_inc(v___x_2794_);
                v___x_2797_ = l_Lean_Syntax_isOfKind(v___x_2794_, v___x_2796_);
                if v___x_2797_ == 0 {
                    crate::leanh::lean_dec(v___x_2794_);
                    crate::leanh::lean_dec(v_attrs_x3f_2790_);
                    crate::leanh::lean_dec(v___y_2789_);
                    crate::leanh::lean_dec(v_stx_1648_);
                    v___x_2798_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                    return v___x_2798_;
                } else {
                    v___x_2799_ = l_Lean_Syntax_getArg(v___x_2794_, v___x_1926_);
                    crate::leanh::lean_dec(v___x_2794_);
                    v___x_2800_ = l_Lean_Syntax_matchesNull(v___x_2799_, v___x_1926_);
                    if v___x_2800_ == 0 {
                        crate::leanh::lean_dec(v_attrs_x3f_2790_);
                        crate::leanh::lean_dec(v___y_2789_);
                        crate::leanh::lean_dec(v_stx_1648_);
                        v___x_2801_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                        return v___x_2801_;
                    } else {
                        v___x_2802_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_2803_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2802_);
                        v___x_2804_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__41;
                        crate::leanh::lean_inc(v___x_2803_);
                        v___x_2805_ = l_Lean_Syntax_isOfKind(v___x_2803_, v___x_2804_);
                        if v___x_2805_ == 0 {
                            v___x_2806_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__43;
                            crate::leanh::lean_inc(v___x_2803_);
                            v___x_2807_ = l_Lean_Syntax_isOfKind(v___x_2803_, v___x_2806_);
                            if v___x_2807_ == 0 {
                                v___x_2808_ =
                                    l_Lean_Elab_Command_expandMixfix___lam__0___closed__45;
                                crate::leanh::lean_inc(v___x_2803_);
                                v___x_2809_ = l_Lean_Syntax_isOfKind(v___x_2803_, v___x_2808_);
                                if v___x_2809_ == 0 {
                                    v___x_2810_ =
                                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__47;
                                    crate::leanh::lean_inc(v___x_2803_);
                                    v___x_2811_ = l_Lean_Syntax_isOfKind(v___x_2803_, v___x_2810_);
                                    if v___x_2811_ == 0 {
                                        v___x_2812_ =
                                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__49;
                                        v___x_2813_ =
                                            l_Lean_Syntax_isOfKind(v___x_2803_, v___x_2812_);
                                        if v___x_2813_ == 0 {
                                            crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                            crate::leanh::lean_dec(v___y_2789_);
                                            crate::leanh::lean_dec(v_stx_1648_);
                                            v___x_2814_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                            return v___x_2814_;
                                        } else {
                                            v___x_2815_ = crate::leanh::lean_unsigned_to_nat(4);
                                            v___x_2816_ =
                                                l_Lean_Syntax_getArg(v_stx_1648_, v___x_2815_);
                                            v___x_2817_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__51;
                                            crate::leanh::lean_inc(v___x_2816_);
                                            v___x_2818_ =
                                                l_Lean_Syntax_isOfKind(v___x_2816_, v___x_2817_);
                                            if v___x_2818_ == 0 {
                                                crate::leanh::lean_dec(v___x_2816_);
                                                crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                                crate::leanh::lean_dec(v___y_2789_);
                                                crate::leanh::lean_dec(v_stx_1648_);
                                                v___x_2819_ =
                                                    l_Lean_Macro_throwUnsupported___redArg(
                                                        v___y_2792_,
                                                    );
                                                return v___x_2819_;
                                            } else {
                                                v___x_2820_ =
                                                    l_Lean_Syntax_getArg(v___x_2816_, v___y_2788_);
                                                crate::leanh::lean_dec(v___x_2816_);
                                                v___x_2821_ = crate::leanh::lean_unsigned_to_nat(5);
                                                v___x_2822_ =
                                                    l_Lean_Syntax_getArg(v_stx_1648_, v___x_2821_);
                                                v___x_2823_ = l_Lean_Syntax_isNone(v___x_2822_);
                                                if v___x_2823_ == 0 {
                                                    crate::leanh::lean_inc(v___x_2822_);
                                                    v___x_2824_ = l_Lean_Syntax_matchesNull(
                                                        v___x_2822_,
                                                        v___y_2788_,
                                                    );
                                                    if v___x_2824_ == 0 {
                                                        crate::leanh::lean_dec(v___x_2822_);
                                                        crate::leanh::lean_dec(v___x_2820_);
                                                        crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                                        crate::leanh::lean_dec(v___y_2789_);
                                                        crate::leanh::lean_dec(v_stx_1648_);
                                                        v___x_2825_ =
                                                            l_Lean_Macro_throwUnsupported___redArg(
                                                                v___y_2792_,
                                                            );
                                                        return v___x_2825_;
                                                    } else {
                                                        v___x_2826_ = l_Lean_Syntax_getArg(
                                                            v___x_2822_,
                                                            v___x_1926_,
                                                        );
                                                        crate::leanh::lean_dec(v___x_2822_);
                                                        v___x_2827_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                                                        crate::leanh::lean_inc(v___x_2826_);
                                                        v___x_2828_ = l_Lean_Syntax_isOfKind(
                                                            v___x_2826_,
                                                            v___x_2827_,
                                                        );
                                                        if v___x_2828_ == 0 {
                                                            crate::leanh::lean_dec(v___x_2826_);
                                                            crate::leanh::lean_dec(v___x_2820_);
                                                            crate::leanh::lean_dec(
                                                                v_attrs_x3f_2790_,
                                                            );
                                                            crate::leanh::lean_dec(v___y_2789_);
                                                            crate::leanh::lean_dec(v_stx_1648_);
                                                            v___x_2829_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                                            return v___x_2829_;
                                                        } else {
                                                            v_name_2830_ = l_Lean_Syntax_getArg(
                                                                v___x_2826_,
                                                                v___x_2802_,
                                                            );
                                                            crate::leanh::lean_dec(v___x_2826_);
                                                            v___x_2831_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_2831_,
                                                                0,
                                                                v_name_2830_,
                                                            );
                                                            v___y_2062_ = v___y_2788_;
                                                            v___y_2063_ = v___x_2796_;
                                                            v___y_2064_ = v___x_2811_;
                                                            v___y_2065_ = v_attrs_x3f_2790_;
                                                            v___y_2066_ = v___x_2817_;
                                                            v___y_2067_ = v___x_2802_;
                                                            v___y_2068_ = v___y_2789_;
                                                            v___y_2069_ = v___x_2795_;
                                                            v___y_2070_ = v___x_2820_;
                                                            v_name_2071_ = v___x_2831_;
                                                            v___y_2072_ = v___y_2791_;
                                                            v___y_2073_ = v___y_2792_;
                                                            state = 10;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v___x_2822_);
                                                    v___x_2832_ = crate::leanh::lean_box(0);
                                                    v___y_2062_ = v___y_2788_;
                                                    v___y_2063_ = v___x_2796_;
                                                    v___y_2064_ = v___x_2811_;
                                                    v___y_2065_ = v_attrs_x3f_2790_;
                                                    v___y_2066_ = v___x_2817_;
                                                    v___y_2067_ = v___x_2802_;
                                                    v___y_2068_ = v___y_2789_;
                                                    v___y_2069_ = v___x_2795_;
                                                    v___y_2070_ = v___x_2820_;
                                                    v_name_2071_ = v___x_2832_;
                                                    v___y_2072_ = v___y_2791_;
                                                    v___y_2073_ = v___y_2792_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_2803_);
                                        v___x_2833_ = crate::leanh::lean_unsigned_to_nat(4);
                                        v___x_2834_ =
                                            l_Lean_Syntax_getArg(v_stx_1648_, v___x_2833_);
                                        v___x_2835_ =
                                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__51;
                                        crate::leanh::lean_inc(v___x_2834_);
                                        v___x_2836_ =
                                            l_Lean_Syntax_isOfKind(v___x_2834_, v___x_2835_);
                                        if v___x_2836_ == 0 {
                                            crate::leanh::lean_dec(v___x_2834_);
                                            crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                            crate::leanh::lean_dec(v___y_2789_);
                                            crate::leanh::lean_dec(v_stx_1648_);
                                            v___x_2837_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                            return v___x_2837_;
                                        } else {
                                            v___x_2838_ =
                                                l_Lean_Syntax_getArg(v___x_2834_, v___y_2788_);
                                            crate::leanh::lean_dec(v___x_2834_);
                                            v___x_2839_ = crate::leanh::lean_unsigned_to_nat(5);
                                            v___x_2840_ =
                                                l_Lean_Syntax_getArg(v_stx_1648_, v___x_2839_);
                                            v___x_2841_ = l_Lean_Syntax_isNone(v___x_2840_);
                                            if v___x_2841_ == 0 {
                                                crate::leanh::lean_inc(v___x_2840_);
                                                v___x_2842_ = l_Lean_Syntax_matchesNull(
                                                    v___x_2840_,
                                                    v___y_2788_,
                                                );
                                                if v___x_2842_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2840_);
                                                    crate::leanh::lean_dec(v___x_2838_);
                                                    crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                                    crate::leanh::lean_dec(v___y_2789_);
                                                    crate::leanh::lean_dec(v_stx_1648_);
                                                    v___x_2843_ =
                                                        l_Lean_Macro_throwUnsupported___redArg(
                                                            v___y_2792_,
                                                        );
                                                    return v___x_2843_;
                                                } else {
                                                    v___x_2844_ = l_Lean_Syntax_getArg(
                                                        v___x_2840_,
                                                        v___x_1926_,
                                                    );
                                                    crate::leanh::lean_dec(v___x_2840_);
                                                    v___x_2845_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                                                    crate::leanh::lean_inc(v___x_2844_);
                                                    v___x_2846_ = l_Lean_Syntax_isOfKind(
                                                        v___x_2844_,
                                                        v___x_2845_,
                                                    );
                                                    if v___x_2846_ == 0 {
                                                        crate::leanh::lean_dec(v___x_2844_);
                                                        crate::leanh::lean_dec(v___x_2838_);
                                                        crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                                        crate::leanh::lean_dec(v___y_2789_);
                                                        crate::leanh::lean_dec(v_stx_1648_);
                                                        v___x_2847_ =
                                                            l_Lean_Macro_throwUnsupported___redArg(
                                                                v___y_2792_,
                                                            );
                                                        return v___x_2847_;
                                                    } else {
                                                        v_name_2848_ = l_Lean_Syntax_getArg(
                                                            v___x_2844_,
                                                            v___x_2802_,
                                                        );
                                                        crate::leanh::lean_dec(v___x_2844_);
                                                        v___x_2849_ = crate::leanh::lean_alloc_ctor(
                                                            1,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2849_,
                                                            0,
                                                            v_name_2848_,
                                                        );
                                                        v___y_2221_ = v___y_2788_;
                                                        v___y_2222_ = v___x_2796_;
                                                        v___y_2223_ = v___x_2838_;
                                                        v___y_2224_ = v_attrs_x3f_2790_;
                                                        v___y_2225_ = v___x_2809_;
                                                        v___y_2226_ = v___x_2802_;
                                                        v___y_2227_ = v___y_2789_;
                                                        v___y_2228_ = v___x_2795_;
                                                        v___y_2229_ = v___x_2835_;
                                                        v_name_2230_ = v___x_2849_;
                                                        v___y_2231_ = v___y_2791_;
                                                        v___y_2232_ = v___y_2792_;
                                                        state = 15;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v___x_2840_);
                                                v___x_2850_ = crate::leanh::lean_box(0);
                                                v___y_2221_ = v___y_2788_;
                                                v___y_2222_ = v___x_2796_;
                                                v___y_2223_ = v___x_2838_;
                                                v___y_2224_ = v_attrs_x3f_2790_;
                                                v___y_2225_ = v___x_2809_;
                                                v___y_2226_ = v___x_2802_;
                                                v___y_2227_ = v___y_2789_;
                                                v___y_2228_ = v___x_2795_;
                                                v___y_2229_ = v___x_2835_;
                                                v_name_2230_ = v___x_2850_;
                                                v___y_2231_ = v___y_2791_;
                                                v___y_2232_ = v___y_2792_;
                                                state = 15;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2803_);
                                    v___x_2851_ = crate::leanh::lean_unsigned_to_nat(4);
                                    v___x_2852_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2851_);
                                    v___x_2853_ =
                                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__51;
                                    crate::leanh::lean_inc(v___x_2852_);
                                    v___x_2854_ = l_Lean_Syntax_isOfKind(v___x_2852_, v___x_2853_);
                                    if v___x_2854_ == 0 {
                                        crate::leanh::lean_dec(v___x_2852_);
                                        crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                        crate::leanh::lean_dec(v___y_2789_);
                                        crate::leanh::lean_dec(v_stx_1648_);
                                        v___x_2855_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                        return v___x_2855_;
                                    } else {
                                        v___x_2856_ =
                                            l_Lean_Syntax_getArg(v___x_2852_, v___y_2788_);
                                        crate::leanh::lean_dec(v___x_2852_);
                                        v___x_2857_ = crate::leanh::lean_unsigned_to_nat(5);
                                        v___x_2858_ =
                                            l_Lean_Syntax_getArg(v_stx_1648_, v___x_2857_);
                                        v___x_2859_ = l_Lean_Syntax_isNone(v___x_2858_);
                                        if v___x_2859_ == 0 {
                                            crate::leanh::lean_inc(v___x_2858_);
                                            v___x_2860_ =
                                                l_Lean_Syntax_matchesNull(v___x_2858_, v___y_2788_);
                                            if v___x_2860_ == 0 {
                                                crate::leanh::lean_dec(v___x_2858_);
                                                crate::leanh::lean_dec(v___x_2856_);
                                                crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                                crate::leanh::lean_dec(v___y_2789_);
                                                crate::leanh::lean_dec(v_stx_1648_);
                                                v___x_2861_ =
                                                    l_Lean_Macro_throwUnsupported___redArg(
                                                        v___y_2792_,
                                                    );
                                                return v___x_2861_;
                                            } else {
                                                v___x_2862_ =
                                                    l_Lean_Syntax_getArg(v___x_2858_, v___x_1926_);
                                                crate::leanh::lean_dec(v___x_2858_);
                                                v___x_2863_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                                                crate::leanh::lean_inc(v___x_2862_);
                                                v___x_2864_ = l_Lean_Syntax_isOfKind(
                                                    v___x_2862_,
                                                    v___x_2863_,
                                                );
                                                if v___x_2864_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2862_);
                                                    crate::leanh::lean_dec(v___x_2856_);
                                                    crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                                    crate::leanh::lean_dec(v___y_2789_);
                                                    crate::leanh::lean_dec(v_stx_1648_);
                                                    v___x_2865_ =
                                                        l_Lean_Macro_throwUnsupported___redArg(
                                                            v___y_2792_,
                                                        );
                                                    return v___x_2865_;
                                                } else {
                                                    v_name_2866_ = l_Lean_Syntax_getArg(
                                                        v___x_2862_,
                                                        v___x_2802_,
                                                    );
                                                    crate::leanh::lean_dec(v___x_2862_);
                                                    v___x_2867_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2867_,
                                                        0,
                                                        v_name_2866_,
                                                    );
                                                    v___y_2402_ = v___y_2788_;
                                                    v___y_2403_ = v___x_2807_;
                                                    v___y_2404_ = v___x_2796_;
                                                    v___y_2405_ = v___x_2856_;
                                                    v___y_2406_ = v_attrs_x3f_2790_;
                                                    v___y_2407_ = v___x_2802_;
                                                    v___y_2408_ = v___x_2853_;
                                                    v___y_2409_ = v___y_2789_;
                                                    v___y_2410_ = v___x_2795_;
                                                    v_name_2411_ = v___x_2867_;
                                                    v___y_2412_ = v___y_2791_;
                                                    v___y_2413_ = v___y_2792_;
                                                    state = 22;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v___x_2858_);
                                            v___x_2868_ = crate::leanh::lean_box(0);
                                            v___y_2402_ = v___y_2788_;
                                            v___y_2403_ = v___x_2807_;
                                            v___y_2404_ = v___x_2796_;
                                            v___y_2405_ = v___x_2856_;
                                            v___y_2406_ = v_attrs_x3f_2790_;
                                            v___y_2407_ = v___x_2802_;
                                            v___y_2408_ = v___x_2853_;
                                            v___y_2409_ = v___y_2789_;
                                            v___y_2410_ = v___x_2795_;
                                            v_name_2411_ = v___x_2868_;
                                            v___y_2412_ = v___y_2791_;
                                            v___y_2413_ = v___y_2792_;
                                            state = 22;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2803_);
                                v___x_2869_ = crate::leanh::lean_unsigned_to_nat(4);
                                v___x_2870_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2869_);
                                v___x_2871_ =
                                    l_Lean_Elab_Command_expandMixfix___lam__0___closed__51;
                                crate::leanh::lean_inc(v___x_2870_);
                                v___x_2872_ = l_Lean_Syntax_isOfKind(v___x_2870_, v___x_2871_);
                                if v___x_2872_ == 0 {
                                    crate::leanh::lean_dec(v___x_2870_);
                                    crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                    crate::leanh::lean_dec(v___y_2789_);
                                    crate::leanh::lean_dec(v_stx_1648_);
                                    v___x_2873_ =
                                        l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                    return v___x_2873_;
                                } else {
                                    v___x_2874_ = l_Lean_Syntax_getArg(v___x_2870_, v___y_2788_);
                                    crate::leanh::lean_dec(v___x_2870_);
                                    v___x_2875_ = crate::leanh::lean_unsigned_to_nat(5);
                                    v___x_2876_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2875_);
                                    v___x_2877_ = l_Lean_Syntax_isNone(v___x_2876_);
                                    if v___x_2877_ == 0 {
                                        crate::leanh::lean_inc(v___x_2876_);
                                        v___x_2878_ =
                                            l_Lean_Syntax_matchesNull(v___x_2876_, v___y_2788_);
                                        if v___x_2878_ == 0 {
                                            crate::leanh::lean_dec(v___x_2876_);
                                            crate::leanh::lean_dec(v___x_2874_);
                                            crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                            crate::leanh::lean_dec(v___y_2789_);
                                            crate::leanh::lean_dec(v_stx_1648_);
                                            v___x_2879_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                            return v___x_2879_;
                                        } else {
                                            v___x_2880_ =
                                                l_Lean_Syntax_getArg(v___x_2876_, v___x_1926_);
                                            crate::leanh::lean_dec(v___x_2876_);
                                            v___x_2881_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                                            crate::leanh::lean_inc(v___x_2880_);
                                            v___x_2882_ =
                                                l_Lean_Syntax_isOfKind(v___x_2880_, v___x_2881_);
                                            if v___x_2882_ == 0 {
                                                crate::leanh::lean_dec(v___x_2880_);
                                                crate::leanh::lean_dec(v___x_2874_);
                                                crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                                crate::leanh::lean_dec(v___y_2789_);
                                                crate::leanh::lean_dec(v_stx_1648_);
                                                v___x_2883_ =
                                                    l_Lean_Macro_throwUnsupported___redArg(
                                                        v___y_2792_,
                                                    );
                                                return v___x_2883_;
                                            } else {
                                                v_name_2884_ =
                                                    l_Lean_Syntax_getArg(v___x_2880_, v___x_2802_);
                                                crate::leanh::lean_dec(v___x_2880_);
                                                v___x_2885_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2885_,
                                                    0,
                                                    v_name_2884_,
                                                );
                                                v___y_2583_ = v___y_2788_;
                                                v___y_2584_ = v___x_2871_;
                                                v___y_2585_ = v___x_2796_;
                                                v___y_2586_ = v___x_2874_;
                                                v___y_2587_ = v___x_2805_;
                                                v___y_2588_ = v_attrs_x3f_2790_;
                                                v___y_2589_ = v___x_2802_;
                                                v___y_2590_ = v___y_2789_;
                                                v___y_2591_ = v___x_2795_;
                                                v_name_2592_ = v___x_2885_;
                                                v___y_2593_ = v___y_2791_;
                                                v___y_2594_ = v___y_2792_;
                                                state = 29;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_2876_);
                                        v___x_2886_ = crate::leanh::lean_box(0);
                                        v___y_2583_ = v___y_2788_;
                                        v___y_2584_ = v___x_2871_;
                                        v___y_2585_ = v___x_2796_;
                                        v___y_2586_ = v___x_2874_;
                                        v___y_2587_ = v___x_2805_;
                                        v___y_2588_ = v_attrs_x3f_2790_;
                                        v___y_2589_ = v___x_2802_;
                                        v___y_2590_ = v___y_2789_;
                                        v___y_2591_ = v___x_2795_;
                                        v_name_2592_ = v___x_2886_;
                                        v___y_2593_ = v___y_2791_;
                                        v___y_2594_ = v___y_2792_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2803_);
                            v___x_2887_ = crate::leanh::lean_unsigned_to_nat(4);
                            v___x_2888_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2887_);
                            v___x_2889_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__51;
                            crate::leanh::lean_inc(v___x_2888_);
                            v___x_2890_ = l_Lean_Syntax_isOfKind(v___x_2888_, v___x_2889_);
                            if v___x_2890_ == 0 {
                                crate::leanh::lean_dec(v___x_2888_);
                                crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                crate::leanh::lean_dec(v___y_2789_);
                                crate::leanh::lean_dec(v_stx_1648_);
                                v___x_2891_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                return v___x_2891_;
                            } else {
                                v___x_2892_ = l_Lean_Syntax_getArg(v___x_2888_, v___y_2788_);
                                crate::leanh::lean_dec(v___x_2888_);
                                v___x_2893_ = crate::leanh::lean_unsigned_to_nat(5);
                                v___x_2894_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2893_);
                                v___x_2895_ = l_Lean_Syntax_isNone(v___x_2894_);
                                if v___x_2895_ == 0 {
                                    crate::leanh::lean_inc(v___x_2894_);
                                    v___x_2896_ =
                                        l_Lean_Syntax_matchesNull(v___x_2894_, v___y_2788_);
                                    if v___x_2896_ == 0 {
                                        crate::leanh::lean_dec(v___x_2894_);
                                        crate::leanh::lean_dec(v___x_2892_);
                                        crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                        crate::leanh::lean_dec(v___y_2789_);
                                        crate::leanh::lean_dec(v_stx_1648_);
                                        v___x_2897_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                        return v___x_2897_;
                                    } else {
                                        v___x_2898_ =
                                            l_Lean_Syntax_getArg(v___x_2894_, v___x_1926_);
                                        crate::leanh::lean_dec(v___x_2894_);
                                        v___x_2899_ =
                                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                                        crate::leanh::lean_inc(v___x_2898_);
                                        v___x_2900_ =
                                            l_Lean_Syntax_isOfKind(v___x_2898_, v___x_2899_);
                                        if v___x_2900_ == 0 {
                                            crate::leanh::lean_dec(v___x_2898_);
                                            crate::leanh::lean_dec(v___x_2892_);
                                            crate::leanh::lean_dec(v_attrs_x3f_2790_);
                                            crate::leanh::lean_dec(v___y_2789_);
                                            crate::leanh::lean_dec(v_stx_1648_);
                                            v___x_2901_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                            return v___x_2901_;
                                        } else {
                                            v_name_2902_ =
                                                l_Lean_Syntax_getArg(v___x_2898_, v___x_2802_);
                                            crate::leanh::lean_dec(v___x_2898_);
                                            v___x_2903_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2903_,
                                                0,
                                                v_name_2902_,
                                            );
                                            v___y_2764_ = v___y_2788_;
                                            v___y_2765_ = v___x_2796_;
                                            v___y_2766_ = v___x_2892_;
                                            v___y_2767_ = v_attrs_x3f_2790_;
                                            v___y_2768_ = v___x_2802_;
                                            v___y_2769_ = v___x_2889_;
                                            v___y_2770_ = v___y_2789_;
                                            v___y_2771_ = v___x_2795_;
                                            v_name_2772_ = v___x_2903_;
                                            v___y_2773_ = v___y_2791_;
                                            v___y_2774_ = v___y_2792_;
                                            state = 36;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2894_);
                                    v___x_2904_ = crate::leanh::lean_box(0);
                                    v___y_2764_ = v___y_2788_;
                                    v___y_2765_ = v___x_2796_;
                                    v___y_2766_ = v___x_2892_;
                                    v___y_2767_ = v_attrs_x3f_2790_;
                                    v___y_2768_ = v___x_2802_;
                                    v___y_2769_ = v___x_2889_;
                                    v___y_2770_ = v___y_2789_;
                                    v___y_2771_ = v___x_2795_;
                                    v_name_2772_ = v___x_2904_;
                                    v___y_2773_ = v___y_2791_;
                                    v___y_2774_ = v___y_2792_;
                                    state = 36;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            38 => {
                v___x_2909_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2910_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2909_);
                v___x_2911_ = l_Lean_Syntax_isNone(v___x_2910_);
                if v___x_2911_ == 0 {
                    crate::leanh::lean_inc(v___x_2910_);
                    v___x_2912_ = l_Lean_Syntax_matchesNull(v___x_2910_, v___x_2909_);
                    if v___x_2912_ == 0 {
                        crate::leanh::lean_dec(v___x_2910_);
                        crate::leanh::lean_dec(v_doc_x3f_2906_);
                        crate::leanh::lean_dec(v_stx_1648_);
                        v___x_2913_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2908_);
                        return v___x_2913_;
                    } else {
                        v___x_2914_ = l_Lean_Syntax_getArg(v___x_2910_, v___x_1926_);
                        crate::leanh::lean_dec(v___x_2910_);
                        v___x_2915_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__52;
                        crate::leanh::lean_inc(v___x_2914_);
                        v___x_2916_ = l_Lean_Syntax_isOfKind(v___x_2914_, v___x_2915_);
                        if v___x_2916_ == 0 {
                            crate::leanh::lean_dec(v___x_2914_);
                            crate::leanh::lean_dec(v_doc_x3f_2906_);
                            crate::leanh::lean_dec(v_stx_1648_);
                            v___x_2917_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2908_);
                            return v___x_2917_;
                        } else {
                            v___x_2918_ = l_Lean_Syntax_getArg(v___x_2914_, v___x_2909_);
                            crate::leanh::lean_dec(v___x_2914_);
                            v_attrs_x3f_2919_ = l_Lean_Syntax_getArgs(v___x_2918_);
                            crate::leanh::lean_dec(v___x_2918_);
                            v___x_2920_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2920_, 0, v_attrs_x3f_2919_);
                            v___y_2788_ = v___x_2909_;
                            v___y_2789_ = v_doc_x3f_2906_;
                            v_attrs_x3f_2790_ = v___x_2920_;
                            v___y_2791_ = v___y_2907_;
                            v___y_2792_ = v___y_2908_;
                            state = 37;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2910_);
                    v___x_2921_ = crate::leanh::lean_box(0);
                    v___y_2788_ = v___x_2909_;
                    v___y_2789_ = v_doc_x3f_2906_;
                    v_attrs_x3f_2790_ = v___x_2921_;
                    v___y_2791_ = v___y_2907_;
                    v___y_2792_ = v___y_2908_;
                    state = 37;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_expandMixfix___lam__0___boxed(
    mut v_stx_2933_: *mut crate::leanh::LeanObject,
    mut v___y_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2936_ = l_Lean_Elab_Command_expandMixfix___lam__0(v_stx_2933_, v___y_2934_, v___y_2935_);
    crate::leanh::lean_dec_ref(v___y_2934_);
    return v_res_2936_;
}
pub unsafe fn l_Lean_Elab_Command_expandMixfix(
    mut v_stx_2938_: *mut crate::leanh::LeanObject,
    mut v_a_2939_: *mut crate::leanh::LeanObject,
    mut v_a_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2941_ = l_Lean_Elab_Command_expandMixfix___closed__0;
    v___x_2942_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(
        v_stx_2938_,
        v___f_2941_,
        v_a_2939_,
        v_a_2940_,
    );
    return v___x_2942_;
}
pub unsafe fn l_Lean_Elab_Command_expandMixfix___boxed(
    mut v_stx_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2946_ = l_Lean_Elab_Command_expandMixfix(v_stx_2943_, v_a_2944_, v_a_2945_);
    crate::leanh::lean_dec_ref(v_a_2944_);
    return v_res_2946_;
}
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2955_ = l_Lean_Elab_macroAttribute;
    v___x_2956_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__17;
    v___x_2957_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2;
    v___x_2958_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_expandMixfix___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_2959_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2955_,
        v___x_2956_,
        v___x_2957_,
        v___x_2958_,
    );
    return v___x_2959_;
}
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___boxed(
    mut v_a_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2961_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
    return v_res_2961_;
}
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2988_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2;
    v___x_2989_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6;
    v___x_2990_ = l_Lean_addBuiltinDeclarationRanges(v___x_2988_, v___x_2989_);
    return v___x_2990_;
}
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___boxed(
    mut v_a_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2992_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
    return v_res_2992_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Mixfix(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Mixfix(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Mixfix(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Mixfix(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Mixfix(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Mixfix(builtin);
}

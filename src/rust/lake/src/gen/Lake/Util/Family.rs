// Lean compiler output
// Module: Lake.Util.Family
// Imports: Init.Data.ToString.Name Init.Data.ToString Init.Notation
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity, lean_string_append};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name,
    l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_mkApp, l_Lean_TSyntax_getId, l_Lean_mkIdentFrom,
};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Macro_resolveGlobalName,
    l_Lean_Macro_throwErrorAt___redArg, l_Lean_Name_append, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_Lean_addMacroScope,
    l_Lean_extractMacroScopes, l_String_toRawSubstring_x27,
};
pub static l_Lake_familyDef___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_familyDef___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__1_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [102, 97, 109, 105, 108, 121, 68, 101, 102, 0],
    };
static mut l_Lake_familyDef___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lake_familyDef___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_familyDef___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_familyDef___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_familyDef___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11046805638130364475 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__3_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lake_familyDef___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_familyDef___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__5_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
    };
static mut l_Lake_familyDef___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_familyDef___closed__5_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__7_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
    };
static mut l_Lake_familyDef___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_familyDef___closed__7_value)
                as *mut crate::leanh::LeanObject,
            3961966953292576997 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_familyDef___closed__8_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_familyDef___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_familyDef___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__11_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [102, 97, 109, 105, 108, 121, 95, 100, 101, 102, 32, 0],
    };
static mut l_Lake_familyDef___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__12_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_familyDef___closed__11_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_familyDef___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__13_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_familyDef___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__14_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Lake_familyDef___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_familyDef___closed__14_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__16_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_familyDef___closed__15_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_familyDef___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__17_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_familyDef___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__18_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [32, 58, 32, 0],
    };
static mut l_Lake_familyDef___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_familyDef___closed__18_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_familyDef___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__20_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_familyDef___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__21_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_familyDef___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__20_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__22_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lake_familyDef___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_familyDef___closed__22_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__24_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_familyDef___closed__23_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__25_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_familyDef___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__21_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__26_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lake_familyDef___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__27_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_familyDef___closed__26_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_familyDef___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__28_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_familyDef___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__25_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__27_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__29_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_familyDef___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__28_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_familyDef___closed__30_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_familyDef___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_familyDef___closed__29_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_familyDef___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__30_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_familyDef: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_familyDef___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__1_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [64, 91, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__7_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 120, 105, 111, 109, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__10_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__11_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__12_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__13_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__14_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__15_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 61, 95, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__15_value) as *mut crate::leanh::LeanObject,5677895497334651815 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [61, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__18_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__19_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__19_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [70, 97, 109, 105, 108, 121, 68, 101, 102, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20_value
) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20_value) as *mut crate::leanh::LeanObject,14062987408811487381 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__22_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_familyDef___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20_value) as *mut crate::leanh::LeanObject,13678286827328889081 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__24_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__24_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__25_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__25_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__26_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__25_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__26_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__27_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__24_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__26_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__27_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__28_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__28_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__29_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__29_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__30_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__30_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__31_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__31_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__32_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__32_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__33_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__33_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__34_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__34_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__35_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [95, 114, 111, 111, 116, 95, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__35_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__36_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__35_value) as *mut crate::leanh::LeanObject,626731335300788152 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__36_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__37_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__37_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__37_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__38_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__42_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__42:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__42_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__42_value) as *mut crate::leanh::LeanObject,8497769072906204829 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__44_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__44:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__44_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__44_value) as *mut crate::leanh::LeanObject,14557702332550915328 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value
) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__47_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__47:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__47_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__48_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 102, 97, 109, 105, 108, 121, 32, 96, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__48:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__48_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__49_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__49:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__49_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_448_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20;
    v___x_449_ = l_String_toRawSubstring_x27(v___x_448_);
    return v___x_449_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46()
-> *mut crate::leanh::LeanObject {
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_494_;
}
pub unsafe fn l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1(
    mut v_x_499_: *mut crate::leanh::LeanObject,
    mut v_a_500_: *mut crate::leanh::LeanObject,
    mut v_a_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: u8 = 0;
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fam_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: u8 = 0;
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_668_: u8 = 0;
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_672_: u8 = 0;
    let mut v_a_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_681_: u8 = 0;
    let mut v_a_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_686_: u8 = 0;
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_690_: u8 = 0;
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_696_: u8 = 0;
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_502_ = l_Lake_familyDef___closed__2;
                crate::leanh::lean_inc(v_x_499_);
                v___x_503_ = l_Lean_Syntax_isOfKind(v_x_499_, v___x_502_);
                if v___x_503_ == 0 {
                    crate::leanh::lean_dec(v_x_499_);
                    v___x_504_ = crate::leanh::lean_box(1);
                    v___x_505_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_505_, 0, v___x_504_);
                    crate::leanh::lean_ctor_set(v___x_505_, 1, v_a_501_);
                    return v___x_505_;
                } else {
                    v___x_506_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_507_ = l_Lean_Syntax_getArg(v_x_499_, v___x_506_);
                    v___x_508_ = crate::leanh::lean_unsigned_to_nat(2);
                    v_id_509_ = l_Lean_Syntax_getArg(v_x_499_, v___x_508_);
                    v___x_510_ = crate::leanh::lean_unsigned_to_nat(4);
                    v_fam_511_ = l_Lean_Syntax_getArg(v_x_499_, v___x_510_);
                    v___x_512_ = crate::leanh::lean_unsigned_to_nat(5);
                    v_idx_513_ = l_Lean_Syntax_getArg(v_x_499_, v___x_512_);
                    v___x_514_ = crate::leanh::lean_unsigned_to_nat(7);
                    v___x_515_ = l_Lean_Syntax_getArg(v_x_499_, v___x_514_);
                    crate::leanh::lean_dec(v_x_499_);
                    v___x_691_ = l_Lean_Syntax_getOptional_x3f(v___x_507_);
                    crate::leanh::lean_dec(v___x_507_);
                    if crate::leanh::lean_obj_tag(v___x_691_) == 0 {
                        v___x_692_ = crate::leanh::lean_box(0);
                        v___y_624_ = v___x_692_;
                        state = 2;
                        continue;
                    } else {
                        v_val_693_ = crate::leanh::lean_ctor_get(v___x_691_, 0);
                        v_isSharedCheck_700_ = (!crate::leanh::lean_is_exclusive(v___x_691_)) as u8;
                        if v_isSharedCheck_700_ == 0 {
                            v___x_695_ = v___x_691_;
                            v_isShared_696_ = v_isSharedCheck_700_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_693_);
                            crate::leanh::lean_dec(v___x_691_);
                            v___x_695_ = crate::leanh::lean_box(0);
                            v_isShared_696_ = v_isSharedCheck_700_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v___y_521_, 2);
                v___x_531_ = l_Array_append___redArg(v___y_521_, v___y_530_);
                crate::leanh::lean_dec_ref(v___y_530_);
                crate::leanh::lean_inc_n(v___y_527_, 9);
                crate::leanh::lean_inc_n(v___y_529_, 39);
                v___x_532_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_532_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_532_, 1, v___y_527_);
                crate::leanh::lean_ctor_set(v___x_532_, 2, v___x_531_);
                v___x_533_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__0;
                v___x_534_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__1;
                crate::leanh::lean_inc_ref_n(v___y_519_, 14);
                crate::leanh::lean_inc_ref_n(v___y_525_, 14);
                v___x_535_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___x_533_, v___x_534_);
                v___x_536_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__2;
                v___x_537_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_537_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_537_, 1, v___x_536_);
                v___x_538_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__3;
                v___x_539_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___x_533_, v___x_538_);
                v___x_540_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__4;
                v___x_541_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___x_533_, v___x_540_);
                v___x_542_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_542_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_542_, 1, v___y_527_);
                crate::leanh::lean_ctor_set(v___x_542_, 2, v___y_521_);
                crate::leanh::lean_inc_ref_n(v___x_542_, 20);
                v___x_543_ = l_Lean_Syntax_node1(v___y_529_, v___x_541_, v___x_542_);
                v___x_544_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__5;
                v___x_545_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__6;
                v___x_546_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___x_544_, v___x_545_);
                v___x_547_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_547_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_547_, 1, v___x_545_);
                v___x_548_ = l_Lean_Syntax_node4(
                    v___y_529_, v___x_546_, v___x_547_, v___x_542_, v___x_542_, v___x_542_,
                );
                crate::leanh::lean_inc(v___x_543_);
                v___x_549_ = l_Lean_Syntax_node2(v___y_529_, v___x_539_, v___x_543_, v___x_548_);
                v___x_550_ = l_Lean_Syntax_node1(v___y_529_, v___y_527_, v___x_549_);
                v___x_551_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__7;
                v___x_552_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_552_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_552_, 1, v___x_551_);
                v___x_553_ =
                    l_Lean_Syntax_node3(v___y_529_, v___x_535_, v___x_537_, v___x_550_, v___x_552_);
                v___x_554_ = l_Lean_Syntax_node1(v___y_529_, v___y_527_, v___x_553_);
                v___x_555_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__8;
                crate::leanh::lean_inc_ref_n(v___y_520_, 6);
                v___x_556_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___y_520_, v___x_555_);
                v___x_557_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_557_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_557_, 1, v___x_555_);
                v___x_558_ = l_Lean_Syntax_node1(v___y_529_, v___x_556_, v___x_557_);
                v___x_559_ = l_Lean_Syntax_node1(v___y_529_, v___y_527_, v___x_558_);
                crate::leanh::lean_inc(v___x_559_);
                crate::leanh::lean_inc_n(v___y_524_, 2);
                v___x_560_ = l_Lean_Syntax_node7(
                    v___y_529_, v___y_524_, v___x_532_, v___x_554_, v___x_559_, v___x_542_,
                    v___x_542_, v___x_542_, v___x_542_,
                );
                v___x_561_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__9;
                v___x_562_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___y_520_, v___x_561_);
                v___x_563_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_563_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_563_, 1, v___x_561_);
                v___x_564_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__10;
                v___x_565_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___y_520_, v___x_564_);
                v___x_566_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__11;
                v___x_567_ = crate::leanh::lean_box(2);
                v___x_568_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
                crate::leanh::lean_ctor_set(v___x_568_, 1, v___y_527_);
                crate::leanh::lean_ctor_set(v___x_568_, 2, v___x_566_);
                v___x_569_ = lean_mk_empty_array_with_capacity(v___x_508_);
                crate::leanh::lean_inc(v___y_526_);
                v___x_570_ = lean_array_push(v___x_569_, v___y_526_);
                v___x_571_ = lean_array_push(v___x_570_, v___x_568_);
                v___x_572_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_572_, 0, v___x_567_);
                crate::leanh::lean_ctor_set(v___x_572_, 1, v___x_565_);
                crate::leanh::lean_ctor_set(v___x_572_, 2, v___x_571_);
                v___x_573_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__12;
                v___x_574_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___y_520_, v___x_573_);
                v___x_575_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__13;
                v___x_576_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___x_533_, v___x_575_);
                v___x_577_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__14;
                v___x_578_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_578_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_578_, 1, v___x_577_);
                v___x_579_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__16;
                v___x_580_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__17;
                v___x_581_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_581_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_581_, 1, v___x_580_);
                crate::leanh::lean_inc(v___x_515_);
                v___x_582_ =
                    l_Lean_Syntax_node3(v___y_529_, v___x_579_, v___y_517_, v___x_581_, v___x_515_);
                crate::leanh::lean_inc_ref(v___x_578_);
                crate::leanh::lean_inc(v___x_576_);
                v___x_583_ = l_Lean_Syntax_node2(v___y_529_, v___x_576_, v___x_578_, v___x_582_);
                crate::leanh::lean_inc(v___x_574_);
                v___x_584_ = l_Lean_Syntax_node2(v___y_529_, v___x_574_, v___x_542_, v___x_583_);
                v___x_585_ =
                    l_Lean_Syntax_node3(v___y_529_, v___x_562_, v___x_563_, v___x_572_, v___x_584_);
                crate::leanh::lean_inc_n(v___y_528_, 2);
                v___x_586_ = l_Lean_Syntax_node2(v___y_529_, v___y_528_, v___x_560_, v___x_585_);
                v___x_587_ = l_Lean_Syntax_node7(
                    v___y_529_, v___y_524_, v___x_542_, v___x_542_, v___x_559_, v___x_542_,
                    v___x_542_, v___x_542_, v___x_542_,
                );
                v___x_588_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__18;
                v___x_589_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___y_520_, v___x_588_);
                v___x_590_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_590_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_590_, 1, v___x_588_);
                v___x_591_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__19;
                v___x_592_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___x_533_, v___x_591_);
                v___x_593_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21_once), _init_l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21);
                v___x_594_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__22;
                crate::leanh::lean_inc(v___y_522_);
                crate::leanh::lean_inc(v___y_518_);
                v___x_595_ = l_Lean_addMacroScope(v___y_518_, v___x_594_, v___y_522_);
                v___x_596_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__27;
                v___x_597_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_597_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_597_, 1, v___x_593_);
                crate::leanh::lean_ctor_set(v___x_597_, 2, v___x_595_);
                crate::leanh::lean_ctor_set(v___x_597_, 3, v___x_596_);
                v___x_598_ =
                    l_Lean_Syntax_node3(v___y_529_, v___y_527_, v_fam_511_, v_idx_513_, v___x_515_);
                v___x_599_ = l_Lean_Syntax_node2(v___y_529_, v___x_592_, v___x_597_, v___x_598_);
                v___x_600_ = l_Lean_Syntax_node2(v___y_529_, v___x_576_, v___x_578_, v___x_599_);
                v___x_601_ = l_Lean_Syntax_node2(v___y_529_, v___x_574_, v___x_542_, v___x_600_);
                v___x_602_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__28;
                v___x_603_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___y_520_, v___x_602_);
                v___x_604_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__29;
                v___x_605_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_605_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_605_, 1, v___x_604_);
                v___x_606_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__30;
                v___x_607_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___x_533_, v___x_606_);
                v___x_608_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__31;
                v___x_609_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_609_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_609_, 1, v___x_608_);
                v___x_610_ = l_Lean_Syntax_node1(v___y_529_, v___y_527_, v___y_526_);
                v___x_611_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__32;
                v___x_612_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_612_, 0, v___y_529_);
                crate::leanh::lean_ctor_set(v___x_612_, 1, v___x_611_);
                v___x_613_ =
                    l_Lean_Syntax_node3(v___y_529_, v___x_607_, v___x_609_, v___x_610_, v___x_612_);
                v___x_614_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__33;
                v___x_615_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__34;
                v___x_616_ = l_Lean_Name_mkStr4(v___y_525_, v___y_519_, v___x_614_, v___x_615_);
                v___x_617_ = l_Lean_Syntax_node2(v___y_529_, v___x_616_, v___x_542_, v___x_542_);
                v___x_618_ = l_Lean_Syntax_node4(
                    v___y_529_, v___x_603_, v___x_605_, v___x_613_, v___x_617_, v___x_542_,
                );
                v___x_619_ = l_Lean_Syntax_node6(
                    v___y_529_, v___x_589_, v___x_543_, v___x_590_, v___x_542_, v___x_542_,
                    v___x_601_, v___x_618_,
                );
                v___x_620_ = l_Lean_Syntax_node2(v___y_529_, v___y_528_, v___x_587_, v___x_619_);
                v___x_621_ = l_Lean_Syntax_node2(v___y_529_, v___y_527_, v___x_586_, v___x_620_);
                v___x_622_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_622_, 0, v___x_621_);
                crate::leanh::lean_ctor_set(v___x_622_, 1, v___y_523_);
                return v___x_622_;
            }
            2 => {
                v___x_625_ = l_Lean_TSyntax_getId(v_fam_511_);
                v___x_626_ = l_Lean_extractMacroScopes(v___x_625_);
                v_name_627_ = crate::leanh::lean_ctor_get(v___x_626_, 0);
                crate::leanh::lean_inc_n(v_name_627_, 2);
                crate::leanh::lean_dec_ref(v___x_626_);
                v___x_628_ = l_Lean_Macro_resolveGlobalName(v_name_627_, v_a_500_, v_a_501_);
                if crate::leanh::lean_obj_tag(v___x_628_) == 0 {
                    v_a_629_ = crate::leanh::lean_ctor_get(v___x_628_, 0);
                    crate::leanh::lean_inc(v_a_629_);
                    if crate::leanh::lean_obj_tag(v_a_629_) == 1 {
                        crate::leanh::lean_dec(v_name_627_);
                        v_head_630_ = crate::leanh::lean_ctor_get(v_a_629_, 0);
                        crate::leanh::lean_inc(v_head_630_);
                        crate::leanh::lean_dec_ref_known(v_a_629_, 2);
                        v_a_631_ = crate::leanh::lean_ctor_get(v___x_628_, 1);
                        crate::leanh::lean_inc(v_a_631_);
                        crate::leanh::lean_dec_ref_known(v___x_628_, 2);
                        v_fst_632_ = crate::leanh::lean_ctor_get(v_head_630_, 0);
                        crate::leanh::lean_inc(v_fst_632_);
                        crate::leanh::lean_dec(v_head_630_);
                        v_quotContext_633_ = crate::leanh::lean_ctor_get(v_a_500_, 1);
                        v_currMacroScope_634_ = crate::leanh::lean_ctor_get(v_a_500_, 2);
                        v_ref_635_ = crate::leanh::lean_ctor_get(v_a_500_, 5);
                        v___x_636_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_637_ = lean_mk_empty_array_with_capacity(v___x_636_);
                        crate::leanh::lean_inc(v_idx_513_);
                        v___x_638_ = lean_array_push(v___x_637_, v_idx_513_);
                        crate::leanh::lean_inc(v_fam_511_);
                        v___x_639_ = l_Lean_Syntax_mkApp(v_fam_511_, v___x_638_);
                        v___x_640_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__36;
                        v___x_641_ = l_Lean_Name_append(v___x_640_, v_fst_632_);
                        v___x_642_ = l_Lean_TSyntax_getId(v_id_509_);
                        v___x_643_ = l_Lean_Name_append(v___x_641_, v___x_642_);
                        v___x_644_ = l_Lean_mkIdentFrom(v_id_509_, v___x_643_, v___x_503_);
                        crate::leanh::lean_dec(v_id_509_);
                        v___x_645_ = 0;
                        v___x_646_ = l_Lean_SourceInfo_fromRef(v_ref_635_, v___x_645_);
                        v___x_647_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__38;
                        v___x_648_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39;
                        v___x_649_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40;
                        v___x_650_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41;
                        v___x_651_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43;
                        v___x_652_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45;
                        v___x_653_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46_once), _init_l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46);
                        if crate::leanh::lean_obj_tag(v___y_624_) == 1 {
                            v_val_654_ = crate::leanh::lean_ctor_get(v___y_624_, 0);
                            crate::leanh::lean_inc(v_val_654_);
                            crate::leanh::lean_dec_ref_known(v___y_624_, 1);
                            v___x_655_ = l_Array_mkArray1___redArg(v_val_654_);
                            v___y_517_ = v___x_639_;
                            v___y_518_ = v_quotContext_633_;
                            v___y_519_ = v___x_649_;
                            v___y_520_ = v___x_650_;
                            v___y_521_ = v___x_653_;
                            v___y_522_ = v_currMacroScope_634_;
                            v___y_523_ = v_a_631_;
                            v___y_524_ = v___x_652_;
                            v___y_525_ = v___x_648_;
                            v___y_526_ = v___x_644_;
                            v___y_527_ = v___x_647_;
                            v___y_528_ = v___x_651_;
                            v___y_529_ = v___x_646_;
                            v___y_530_ = v___x_655_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_624_);
                            v___x_656_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__47;
                            v___y_517_ = v___x_639_;
                            v___y_518_ = v_quotContext_633_;
                            v___y_519_ = v___x_649_;
                            v___y_520_ = v___x_650_;
                            v___y_521_ = v___x_653_;
                            v___y_522_ = v_currMacroScope_634_;
                            v___y_523_ = v_a_631_;
                            v___y_524_ = v___x_652_;
                            v___y_525_ = v___x_648_;
                            v___y_526_ = v___x_644_;
                            v___y_527_ = v___x_647_;
                            v___y_528_ = v___x_651_;
                            v___y_529_ = v___x_646_;
                            v___y_530_ = v___x_656_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_629_);
                        crate::leanh::lean_dec(v___y_624_);
                        crate::leanh::lean_dec(v___x_515_);
                        crate::leanh::lean_dec(v_idx_513_);
                        crate::leanh::lean_dec(v_id_509_);
                        v_a_657_ = crate::leanh::lean_ctor_get(v___x_628_, 1);
                        crate::leanh::lean_inc(v_a_657_);
                        crate::leanh::lean_dec_ref_known(v___x_628_, 2);
                        v___x_658_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__48;
                        v___x_659_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_627_,
                                v___x_503_,
                            );
                        v___x_660_ = lean_string_append(v___x_658_, v___x_659_);
                        crate::leanh::lean_dec_ref(v___x_659_);
                        v___x_661_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__49;
                        v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
                        v___x_663_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_fam_511_, v___x_662_, v_a_500_, v_a_657_,
                        );
                        crate::leanh::lean_dec(v_fam_511_);
                        if crate::leanh::lean_obj_tag(v___x_663_) == 0 {
                            v_a_664_ = crate::leanh::lean_ctor_get(v___x_663_, 0);
                            v_a_665_ = crate::leanh::lean_ctor_get(v___x_663_, 1);
                            v_isSharedCheck_672_ =
                                (!crate::leanh::lean_is_exclusive(v___x_663_)) as u8;
                            if v_isSharedCheck_672_ == 0 {
                                v___x_667_ = v___x_663_;
                                v_isShared_668_ = v_isSharedCheck_672_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_665_);
                                crate::leanh::lean_inc(v_a_664_);
                                crate::leanh::lean_dec(v___x_663_);
                                v___x_667_ = crate::leanh::lean_box(0);
                                v_isShared_668_ = v_isSharedCheck_672_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_673_ = crate::leanh::lean_ctor_get(v___x_663_, 0);
                            v_a_674_ = crate::leanh::lean_ctor_get(v___x_663_, 1);
                            v_isSharedCheck_681_ =
                                (!crate::leanh::lean_is_exclusive(v___x_663_)) as u8;
                            if v_isSharedCheck_681_ == 0 {
                                v___x_676_ = v___x_663_;
                                v_isShared_677_ = v_isSharedCheck_681_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_674_);
                                crate::leanh::lean_inc(v_a_673_);
                                crate::leanh::lean_dec(v___x_663_);
                                v___x_676_ = crate::leanh::lean_box(0);
                                v_isShared_677_ = v_isSharedCheck_681_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_name_627_);
                    crate::leanh::lean_dec(v___y_624_);
                    crate::leanh::lean_dec(v___x_515_);
                    crate::leanh::lean_dec(v_idx_513_);
                    crate::leanh::lean_dec(v_fam_511_);
                    crate::leanh::lean_dec(v_id_509_);
                    v_a_682_ = crate::leanh::lean_ctor_get(v___x_628_, 0);
                    v_a_683_ = crate::leanh::lean_ctor_get(v___x_628_, 1);
                    v_isSharedCheck_690_ = (!crate::leanh::lean_is_exclusive(v___x_628_)) as u8;
                    if v_isSharedCheck_690_ == 0 {
                        v___x_685_ = v___x_628_;
                        v_isShared_686_ = v_isSharedCheck_690_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_683_);
                        crate::leanh::lean_inc(v_a_682_);
                        crate::leanh::lean_dec(v___x_628_);
                        v___x_685_ = crate::leanh::lean_box(0);
                        v_isShared_686_ = v_isSharedCheck_690_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_668_ == 0 {
                    v___x_670_ = v___x_667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_671_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_664_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_671_, 1, v_a_665_);
                    v___x_670_ = v_reuseFailAlloc_671_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_670_;
            }
            5 => {
                if v_isShared_677_ == 0 {
                    v___x_679_ = v___x_676_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_680_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_680_, 1, v_a_674_);
                    v___x_679_ = v_reuseFailAlloc_680_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_679_;
            }
            7 => {
                if v_isShared_686_ == 0 {
                    v___x_688_ = v___x_685_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_689_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_689_, 1, v_a_683_);
                    v___x_688_ = v_reuseFailAlloc_689_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_688_;
            }
            9 => {
                if v_isShared_696_ == 0 {
                    v___x_698_ = v___x_695_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_699_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_699_, 0, v_val_693_);
                    v___x_698_ = v_reuseFailAlloc_699_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_624_ = v___x_698_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___boxed(
    mut v_x_701_: *mut crate::leanh::LeanObject,
    mut v_a_702_: *mut crate::leanh::LeanObject,
    mut v_a_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_704_ = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1(
        v_x_701_, v_a_702_, v_a_703_,
    );
    crate::leanh::lean_dec_ref(v_a_702_);
    return v_res_704_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Family(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Family(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Family(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Family(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Family(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Family(builtin);
}

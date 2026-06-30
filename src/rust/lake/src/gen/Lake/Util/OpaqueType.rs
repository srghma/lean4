// Lean compiler output
// Module: Lake.Util.OpaqueType
// Imports: Lake.Util.Binder Init.Prelude
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_unzip___redArg};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_mkApp, l_Lean_TSyntax_getId, l_Lean_mkIdentFrom, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    initialize_Init_Prelude, l_Array_mkArray0, l_Array_mkArray1___redArg,
    l_Lean_MacroScopesView_review, l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr4, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_Lean_addMacroScope, l_Lean_extractMacroScopes, l_String_toRawSubstring_x27,
    runtime_initialize_Init_Prelude,
};
use crate::r#gen::Lake::Util::Binder::{
    initialize_Lake_Util_Binder, l_Lake_BinderSyntaxView_mkArgument,
    l_Lake_BinderSyntaxView_mkBinder, l_Lake_expandBinders, runtime_initialize_Lake_Util_Binder,
};
pub static l_Lake_nonemptyTypeCmd___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lake_nonemptyTypeCmd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__1_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            110, 111, 110, 101, 109, 112, 116, 121, 84, 121, 112, 101, 67, 109, 100, 0,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__1_value) as *mut leanh::LeanObject;
static l_Lake_nonemptyTypeCmd___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_nonemptyTypeCmd___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__1_value)
                as *mut leanh::LeanObject,
            2831656807158390110 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__3_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_nonemptyTypeCmd___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__3_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__5_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_nonemptyTypeCmd___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__5_value)
                as *mut leanh::LeanObject,
            18170484695678750185 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__7_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_nonemptyTypeCmd___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__7_value)
                as *mut leanh::LeanObject,
            3961966953292576997 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__9_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__11_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [118, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0],
    };
static mut l_Lake_nonemptyTypeCmd___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__11_value)
                as *mut leanh::LeanObject,
            18370519569176055110 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__13_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__15_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__16_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
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
            110, 111, 110, 101, 109, 112, 116, 121, 95, 116, 121, 112, 101, 32, 0,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__17_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__18_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__18_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__19_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
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
static mut l_Lake_nonemptyTypeCmd___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__20_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__19_value)
                as *mut leanh::LeanObject,
            5117844058249666356 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__21_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__21_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__22_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__18_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__21_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__23_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [109, 97, 110, 121, 0],
    };
static mut l_Lake_nonemptyTypeCmd___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__24_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__23_value)
                as *mut leanh::LeanObject,
            2302572775315350313 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__24_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__25_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [98, 105, 110, 100, 101, 114, 0],
    };
static mut l_Lake_nonemptyTypeCmd___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__25_value) as *mut leanh::LeanObject;
static l_Lake_nonemptyTypeCmd___closed__26_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_nonemptyTypeCmd___closed__26_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__26_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__25_value)
                as *mut leanh::LeanObject,
            16338829057506708314 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__26_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__27_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__26_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__27_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__28_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__24_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__27_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__28_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__29_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__22_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__28_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__29_value) as *mut leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__30_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__2_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__29_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__30_value) as *mut leanh::LeanObject;
pub static mut l_Lake_nonemptyTypeCmd: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__30_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 111, 110, 101, 109, 112, 116, 121, 84, 121, 112, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 110, 115, 116, 78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 121, 112, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 121, 112, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 105, 112, 101, 80, 114, 111, 106, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [124, 62, 46, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3_value) as *mut leanh::LeanObject,11503787708459150704 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16_value) as *mut leanh::LeanObject,13229434762204987278 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 114, 111, 112, 101, 114, 116, 121, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26_value) as *mut leanh::LeanObject,13877162779417220697 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35_value) as *mut leanh::LeanObject,8497769072906204829 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37_value) as *mut leanh::LeanObject,14557702332550915328 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40_value) as *mut leanh::LeanObject,10324751846086867157 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 112, 97, 113, 117, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42_value) as *mut leanh::LeanObject,7407402195942431087 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44_value) as *mut leanh::LeanObject,1827444229220621555 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48_value) as *mut leanh::LeanObject,5940551064397964566 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51_value) as *mut leanh::LeanObject,4498178684837002829 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 85, 110, 105, 118, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54_value) as *mut leanh::LeanObject,4475001683190667726 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [78, 111, 110, 101, 109, 112, 116, 121, 84, 121, 112, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56_value) as *mut leanh::LeanObject,1236407310526250327 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [46, 123, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64_value) as *mut leanh::LeanObject,6110315075117401315 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [48, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67_value) as *mut leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__0_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            104, 121, 100, 114, 97, 116, 101, 79, 112, 97, 113, 117, 101, 84, 121, 112, 101, 67,
            109, 100, 0,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_hydrateOpaqueTypeCmd___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_hydrateOpaqueTypeCmd___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__0_value)
                as *mut leanh::LeanObject,
            1609764115375978371 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__2_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            104, 121, 100, 114, 97, 116, 101, 95, 111, 112, 97, 113, 117, 101, 95, 116, 121, 112,
            101, 32, 0,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__14_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__21_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__21_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__24_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__21_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__9_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_hydrateOpaqueTypeCmd: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__9_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0_value) as *mut leanh::LeanObject,6962862263136859431 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 111, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0_value) as *mut leanh::LeanObject,16059047048258275031 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 104, 97, 98, 105, 116, 101, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value) as *mut leanh::LeanObject,13340093926952294564 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 102, 97, 117, 108, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value) as *mut leanh::LeanObject,9666231177748665885 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value) as *mut leanh::LeanObject,13340093926952294564 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value) as *mut leanh::LeanObject,609174137020324014 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 110, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29_value) as *mut leanh::LeanObject,12500803453736965855 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [117, 110, 115, 97, 102, 101, 77, 107, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,15035602936918917649 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 115, 116, 67, 111, 101, 77, 107, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35_value) as *mut leanh::LeanObject,6447927339206716348 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [103, 101, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38_value) as *mut leanh::LeanObject,699949278435066773 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [117, 110, 115, 97, 102, 101, 71, 101, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41_value) as *mut leanh::LeanObject,15932694652473032876 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 67, 111, 101, 71, 101, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44_value) as *mut leanh::LeanObject,9226533731144894724 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 115, 112, 97, 99, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47_value) as *mut leanh::LeanObject,17575194138276270420 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49_value) as *mut leanh::LeanObject,2533412339571800130 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [64, 91, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52_value) as *mut leanh::LeanObject,7499624980761693169 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14_value) as *mut leanh::LeanObject,7983999284776576032 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55_value) as *mut leanh::LeanObject,4584992172905639687 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56_value) as *mut leanh::LeanObject,3878072352281346923 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 108, 105, 110, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58_value) as *mut leanh::LeanObject,8159932143332935260 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 110, 115, 97, 102, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64_value) as *mut leanh::LeanObject,10398938568477941839 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0_value) as *mut leanh::LeanObject,9789339221525904376 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2_value) as *mut leanh::LeanObject,5473625859156281626 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 114, 111, 119, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70_value) as *mut leanh::LeanObject,14917456309791986358 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 146, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5_value) as *mut leanh::LeanObject,13585030837571646948 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [117, 110, 115, 97, 102, 101, 67, 97, 115, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75_value) as *mut leanh::LeanObject,9183409343678294206 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11_value) as *mut leanh::LeanObject,7625897890118033792 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12_value) as *mut leanh::LeanObject,8715860392475343861 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 95, 98, 121, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81_value) as *mut leanh::LeanObject,5229394285883816413 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0(
    mut v_x_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0;
    v___x_1277_ = l_Lean_Name_str___override(v_x_1275_, v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1(
    mut v_x_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1280_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0;
    v___x_1281_ = l_Lean_Name_str___override(v_x_1279_, v___x_1280_);
    return v___x_1281_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1(
    mut v_sz_1282_: usize,
    mut v_i_1283_: usize,
    mut v_bs_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1285_: u8 = 0;
    let mut v_v_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: usize = 0;
    let mut v___x_1290_: usize = 0;
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1285_ = lean_usize_dec_lt(v_i_1283_, v_sz_1282_);
                if v___x_1285_ == 0 {
                    return v_bs_1284_;
                } else {
                    v_v_1286_ = lean_array_uget(v_bs_1284_, v_i_1283_);
                    v___x_1287_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1288_ = lean_array_uset(v_bs_1284_, v_i_1283_, v___x_1287_);
                    v___x_1289_ = 1usize;
                    v___x_1290_ = lean_usize_add(v_i_1283_, v___x_1289_);
                    v___x_1291_ = lean_array_uset(v_bs_x27_1288_, v_i_1283_, v_v_1286_);
                    v_i_1283_ = v___x_1290_;
                    v_bs_1284_ = v___x_1291_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1___boxed(
    mut v_sz_1293_: *mut leanh::LeanObject,
    mut v_i_1294_: *mut leanh::LeanObject,
    mut v_bs_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1296_: usize = 0;
    let mut v_i_boxed_1297_: usize = 0;
    let mut v_res_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1296_ = leanh::lean_unbox_usize(v_sz_1293_);
    leanh::lean_dec(v_sz_1293_);
    v_i_boxed_1297_ = leanh::lean_unbox_usize(v_i_1294_);
    leanh::lean_dec(v_i_1294_);
    v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1(v_sz_boxed_1296_, v_i_boxed_1297_, v_bs_1295_);
    return v_res_1298_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0(
    mut v_sz_1299_: usize,
    mut v_i_1300_: usize,
    mut v_bs_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1302_: u8 = 0;
    let mut v_v_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: usize = 0;
    let mut v___x_1310_: usize = 0;
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1302_ = lean_usize_dec_lt(v_i_1300_, v_sz_1299_);
                if v___x_1302_ == 0 {
                    return v_bs_1301_;
                } else {
                    v_v_1303_ = lean_array_uget(v_bs_1301_, v_i_1300_);
                    v___x_1304_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1305_ = lean_array_uset(v_bs_1301_, v_i_1300_, v___x_1304_);
                    leanh::lean_inc(v_v_1303_);
                    v___x_1306_ = l_Lake_BinderSyntaxView_mkBinder(v_v_1303_);
                    v___x_1307_ = l_Lake_BinderSyntaxView_mkArgument(v_v_1303_);
                    v___x_1308_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1308_, 0, v___x_1306_);
                    leanh::lean_ctor_set(v___x_1308_, 1, v___x_1307_);
                    v___x_1309_ = 1usize;
                    v___x_1310_ = lean_usize_add(v_i_1300_, v___x_1309_);
                    v___x_1311_ = lean_array_uset(v_bs_x27_1305_, v_i_1300_, v___x_1308_);
                    v_i_1300_ = v___x_1310_;
                    v_bs_1301_ = v___x_1311_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0___boxed(
    mut v_sz_1313_: *mut leanh::LeanObject,
    mut v_i_1314_: *mut leanh::LeanObject,
    mut v_bs_1315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1316_: usize = 0;
    let mut v_i_boxed_1317_: usize = 0;
    let mut v_res_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1316_ = leanh::lean_unbox_usize(v_sz_1313_);
    leanh::lean_dec(v_sz_1313_);
    v_i_boxed_1317_ = leanh::lean_unbox_usize(v_i_1314_);
    leanh::lean_dec(v_i_1314_);
    v_res_1318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0(v_sz_boxed_1316_, v_i_boxed_1317_, v_bs_1315_);
    return v_res_1318_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1328_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3;
    v___x_1329_ = l_String_toRawSubstring_x27(v___x_1328_);
    return v___x_1329_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16;
    v___x_1339_ = l_String_toRawSubstring_x27(v___x_1338_);
    return v___x_1339_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26;
    v___x_1352_ = l_String_toRawSubstring_x27(v___x_1351_);
    return v___x_1352_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_1375_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57()
-> *mut leanh::LeanObject {
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56;
    v___x_1422_ = l_String_toRawSubstring_x27(v___x_1421_);
    return v___x_1422_;
}
pub unsafe fn l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1(
    mut v_x_1442_: *mut leanh::LeanObject,
    mut v_a_1443_: *mut leanh::LeanObject,
    mut v_a_1444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1614_: usize = 0;
    let mut v___y_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1616_: u8 = 0;
    let mut v___y_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1653_: usize = 0;
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1687_: usize = 0;
    let mut v___y_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: u8 = 0;
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_view_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1721_: usize = 0;
    let mut v___x_1722_: usize = 0;
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: u8 = 0;
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_view_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1737_: u8 = 0;
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v_a_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v___y_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1770_: u8 = 0;
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1445_ = l_Lake_nonemptyTypeCmd___closed__2;
                leanh::lean_inc(v_x_1442_);
                v___x_1446_ = l_Lean_Syntax_isOfKind(v_x_1442_, v___x_1445_);
                if v___x_1446_ == 0 {
                    leanh::lean_dec(v_x_1442_);
                    v___x_1447_ = leanh::lean_box(1);
                    v___x_1448_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1448_, 0, v___x_1447_);
                    leanh::lean_ctor_set(v___x_1448_, 1, v_a_1444_);
                    return v___x_1448_;
                } else {
                    v___x_1449_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1450_ = l_Lean_Syntax_getArg(v_x_1442_, v___x_1449_);
                    v___x_1451_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1452_ = l_Lean_Syntax_getArg(v_x_1442_, v___x_1451_);
                    v___x_1453_ = leanh::lean_unsigned_to_nat(3);
                    v_id_1454_ = l_Lean_Syntax_getArg(v_x_1442_, v___x_1453_);
                    v___x_1712_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1713_ = l_Lean_Syntax_getArg(v_x_1442_, v___x_1712_);
                    leanh::lean_dec(v_x_1442_);
                    v_bs_1714_ = l_Lean_Syntax_getArgs(v___x_1713_);
                    leanh::lean_dec(v___x_1713_);
                    v___x_1765_ = l_Lean_Syntax_getOptional_x3f(v___x_1452_);
                    leanh::lean_dec(v___x_1452_);
                    if leanh::lean_obj_tag(v___x_1765_) == 0 {
                        v___x_1766_ = leanh::lean_box(0);
                        v___y_1754_ = v___x_1766_;
                        state = 12;
                        continue;
                    } else {
                        v_val_1767_ = leanh::lean_ctor_get(v___x_1765_, 0);
                        v_isSharedCheck_1774_ =
                            (!leanh::lean_is_exclusive(v___x_1765_)) as u8;
                        if v_isSharedCheck_1774_ == 0 {
                            v___x_1769_ = v___x_1765_;
                            v_isShared_1770_ = v_isSharedCheck_1774_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1767_);
                            leanh::lean_dec(v___x_1765_);
                            v___x_1769_ = leanh::lean_box(0);
                            v_isShared_1770_ = v_isSharedCheck_1774_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1485_ = l_Array_append___redArg(v___y_1458_, v___y_1484_);
                leanh::lean_dec_ref(v___y_1484_);
                leanh::lean_inc_n(v___y_1470_, 5);
                leanh::lean_inc_n(v___y_1475_, 38);
                v___x_1486_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1486_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1486_, 1, v___y_1470_);
                leanh::lean_ctor_set(v___x_1486_, 2, v___x_1485_);
                leanh::lean_inc_ref(v___x_1486_);
                leanh::lean_inc_n(v___y_1472_, 24);
                leanh::lean_inc(v___y_1462_);
                v___x_1487_ = l_Lean_Syntax_node7(
                    v___y_1475_,
                    v___y_1462_,
                    v___y_1483_,
                    v___y_1472_,
                    v___x_1486_,
                    v___y_1472_,
                    v___y_1472_,
                    v___y_1472_,
                    v___y_1472_,
                );
                v___x_1488_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0;
                leanh::lean_inc_ref_n(v___y_1461_, 4);
                leanh::lean_inc_ref_n(v___y_1457_, 13);
                leanh::lean_inc_ref_n(v___y_1479_, 13);
                v___x_1489_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1461_, v___x_1488_);
                v___x_1490_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1;
                v___x_1491_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1491_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1491_, 1, v___x_1490_);
                leanh::lean_inc(v_id_1454_);
                v___x_1492_ = lean_array_push(v___y_1463_, v_id_1454_);
                v___x_1493_ = lean_array_push(v___x_1492_, v___y_1480_);
                leanh::lean_inc_n(v___y_1473_, 2);
                leanh::lean_inc(v___y_1466_);
                v___x_1494_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1494_, 0, v___y_1466_);
                leanh::lean_ctor_set(v___x_1494_, 1, v___y_1473_);
                leanh::lean_ctor_set(v___x_1494_, 2, v___x_1493_);
                v___x_1495_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2;
                v___x_1496_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1461_, v___x_1495_);
                v___x_1497_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3;
                leanh::lean_inc_ref_n(v___y_1464_, 5);
                v___x_1498_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1464_, v___x_1497_);
                v___x_1499_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4;
                v___x_1500_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1500_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1500_, 1, v___x_1499_);
                v___x_1501_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___x_1498_, v___x_1500_, v___y_1472_);
                leanh::lean_inc(v___y_1481_);
                leanh::lean_inc(v___y_1478_);
                v___x_1502_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___y_1478_, v___y_1481_, v___x_1501_);
                v___x_1503_ = l_Lean_Syntax_node1(v___y_1475_, v___y_1470_, v___x_1502_);
                v___x_1504_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___x_1496_, v___y_1471_, v___x_1503_);
                v___x_1505_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5;
                v___x_1506_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1461_, v___x_1505_);
                v___x_1507_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6;
                v___x_1508_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1508_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1508_, 1, v___x_1507_);
                v___x_1509_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7;
                v___x_1510_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1464_, v___x_1509_);
                v___x_1511_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8;
                v___x_1512_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1512_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1512_, 1, v___x_1511_);
                v___x_1513_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9);
                v___x_1514_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10;
                leanh::lean_inc_n(v___y_1459_, 2);
                leanh::lean_inc_n(v___y_1469_, 2);
                v___x_1515_ = l_Lean_addMacroScope(v___y_1469_, v___x_1514_, v___y_1459_);
                leanh::lean_inc_n(v___y_1477_, 3);
                v___x_1516_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1516_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1516_, 1, v___x_1513_);
                leanh::lean_ctor_set(v___x_1516_, 2, v___x_1515_);
                leanh::lean_ctor_set(v___x_1516_, 3, v___y_1477_);
                leanh::lean_inc_ref(v___x_1512_);
                leanh::lean_inc(v___y_1465_);
                leanh::lean_inc(v___x_1510_);
                v___x_1517_ = l_Lean_Syntax_node5(
                    v___y_1475_,
                    v___x_1510_,
                    v___y_1465_,
                    v___x_1512_,
                    v___x_1516_,
                    v___y_1472_,
                    v___y_1472_,
                );
                v___x_1518_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11;
                v___x_1519_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12;
                v___x_1520_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___x_1518_, v___x_1519_);
                v___x_1521_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___x_1520_, v___y_1472_, v___y_1472_);
                leanh::lean_inc(v___x_1521_);
                leanh::lean_inc_ref(v___x_1508_);
                leanh::lean_inc(v___x_1506_);
                v___x_1522_ = l_Lean_Syntax_node4(
                    v___y_1475_,
                    v___x_1506_,
                    v___x_1508_,
                    v___x_1517_,
                    v___x_1521_,
                    v___y_1472_,
                );
                v___x_1523_ = l_Lean_Syntax_node5(
                    v___y_1475_,
                    v___x_1489_,
                    v___x_1491_,
                    v___x_1494_,
                    v___x_1504_,
                    v___x_1522_,
                    v___y_1472_,
                );
                leanh::lean_inc(v___y_1476_);
                v___x_1524_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___y_1476_, v___x_1487_, v___x_1523_);
                v___x_1525_ = l_Lean_Syntax_node7(
                    v___y_1475_,
                    v___y_1462_,
                    v___y_1472_,
                    v___y_1472_,
                    v___x_1486_,
                    v___y_1472_,
                    v___y_1472_,
                    v___y_1472_,
                    v___y_1472_,
                );
                v___x_1526_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13;
                v___x_1527_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1461_, v___x_1526_);
                v___x_1528_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14;
                v___x_1529_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1464_, v___x_1528_);
                v___x_1530_ = l_Lean_Syntax_node1(v___y_1475_, v___x_1529_, v___y_1472_);
                v___x_1531_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1531_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1531_, 1, v___x_1526_);
                v___x_1532_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___y_1473_, v___y_1467_, v___y_1472_);
                v___x_1533_ = l_Lean_Syntax_node1(v___y_1475_, v___y_1470_, v___x_1532_);
                v___x_1534_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15;
                v___x_1535_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1464_, v___x_1534_);
                v___x_1536_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17);
                v___x_1537_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18;
                v___x_1538_ = l_Lean_addMacroScope(v___y_1469_, v___x_1537_, v___y_1459_);
                leanh::lean_inc(v___y_1460_);
                v___x_1539_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1539_, 0, v___x_1537_);
                leanh::lean_ctor_set(v___x_1539_, 1, v___y_1460_);
                v___x_1540_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19;
                v___x_1541_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1541_, 0, v___x_1540_);
                leanh::lean_ctor_set(v___x_1541_, 1, v___y_1477_);
                v___x_1542_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1542_, 0, v___x_1539_);
                leanh::lean_ctor_set(v___x_1542_, 1, v___x_1541_);
                v___x_1543_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1543_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1543_, 1, v___x_1536_);
                leanh::lean_ctor_set(v___x_1543_, 2, v___x_1538_);
                leanh::lean_ctor_set(v___x_1543_, 3, v___x_1542_);
                v___x_1544_ = l_Lean_Syntax_mkApp(v_id_1454_, v___y_1474_);
                v___x_1545_ = l_Lean_Syntax_node1(v___y_1475_, v___y_1470_, v___x_1544_);
                v___x_1546_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___x_1535_, v___x_1543_, v___x_1545_);
                v___x_1547_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___y_1478_, v___y_1481_, v___x_1546_);
                v___x_1548_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___y_1482_, v___y_1472_, v___x_1547_);
                v___x_1549_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20;
                v___x_1550_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1464_, v___x_1549_);
                v___x_1551_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21;
                v___x_1552_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1552_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1552_, 1, v___x_1551_);
                v___x_1553_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22;
                v___x_1554_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23;
                v___x_1555_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___x_1553_, v___x_1554_);
                v___x_1556_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24;
                v___x_1557_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___x_1553_, v___x_1556_);
                v___x_1558_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25;
                v___x_1559_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___x_1553_, v___x_1558_);
                v___x_1560_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1560_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1560_, 1, v___x_1558_);
                v___x_1561_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27);
                v___x_1562_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28;
                v___x_1563_ = l_Lean_addMacroScope(v___y_1469_, v___x_1562_, v___y_1459_);
                v___x_1564_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1564_, 0, v___y_1475_);
                leanh::lean_ctor_set(v___x_1564_, 1, v___x_1561_);
                leanh::lean_ctor_set(v___x_1564_, 2, v___x_1563_);
                leanh::lean_ctor_set(v___x_1564_, 3, v___y_1477_);
                v___x_1565_ = l_Lean_Syntax_node5(
                    v___y_1475_,
                    v___x_1510_,
                    v___y_1465_,
                    v___x_1512_,
                    v___x_1564_,
                    v___y_1472_,
                    v___y_1472_,
                );
                v___x_1566_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___x_1559_, v___x_1560_, v___x_1565_);
                v___x_1567_ = l_Lean_Syntax_node1(v___y_1475_, v___y_1470_, v___x_1566_);
                v___x_1568_ = l_Lean_Syntax_node1(v___y_1475_, v___x_1557_, v___x_1567_);
                v___x_1569_ = l_Lean_Syntax_node1(v___y_1475_, v___x_1555_, v___x_1568_);
                v___x_1570_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___x_1550_, v___x_1552_, v___x_1569_);
                v___x_1571_ = l_Lean_Syntax_node4(
                    v___y_1475_,
                    v___x_1506_,
                    v___x_1508_,
                    v___x_1570_,
                    v___x_1521_,
                    v___y_1472_,
                );
                v___x_1572_ = l_Lean_Syntax_node6(
                    v___y_1475_,
                    v___x_1527_,
                    v___x_1530_,
                    v___x_1531_,
                    v___y_1472_,
                    v___x_1533_,
                    v___x_1548_,
                    v___x_1571_,
                );
                v___x_1573_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___y_1476_, v___x_1525_, v___x_1572_);
                v___x_1574_ = l_Lean_Syntax_node3(
                    v___y_1475_,
                    v___y_1470_,
                    v___y_1456_,
                    v___x_1524_,
                    v___x_1573_,
                );
                v___x_1575_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1575_, 0, v___x_1574_);
                leanh::lean_ctor_set(v___x_1575_, 1, v___y_1468_);
                return v___x_1575_;
            }
            2 => {
                leanh::lean_inc_ref(v___y_1580_);
                v___x_1606_ = l_Array_append___redArg(v___y_1580_, v___y_1605_);
                leanh::lean_dec_ref(v___y_1605_);
                leanh::lean_inc(v___y_1591_);
                leanh::lean_inc(v___y_1596_);
                v___x_1607_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1607_, 0, v___y_1596_);
                leanh::lean_ctor_set(v___x_1607_, 1, v___y_1591_);
                leanh::lean_ctor_set(v___x_1607_, 2, v___x_1606_);
                if leanh::lean_obj_tag(v___y_1601_) == 1 {
                    v_val_1608_ = leanh::lean_ctor_get(v___y_1601_, 0);
                    leanh::lean_inc(v_val_1608_);
                    leanh::lean_dec_ref_known(v___y_1601_, 1);
                    v___x_1609_ = l_Array_mkArray1___redArg(v_val_1608_);
                    v___y_1456_ = v___y_1577_;
                    v___y_1457_ = v___y_1578_;
                    v___y_1458_ = v___y_1580_;
                    v___y_1459_ = v___y_1579_;
                    v___y_1460_ = v___y_1581_;
                    v___y_1461_ = v___y_1582_;
                    v___y_1462_ = v___y_1583_;
                    v___y_1463_ = v___y_1584_;
                    v___y_1464_ = v___y_1585_;
                    v___y_1465_ = v___y_1586_;
                    v___y_1466_ = v___y_1587_;
                    v___y_1467_ = v___y_1588_;
                    v___y_1468_ = v___y_1589_;
                    v___y_1469_ = v___y_1590_;
                    v___y_1470_ = v___y_1591_;
                    v___y_1471_ = v___y_1592_;
                    v___y_1472_ = v___y_1593_;
                    v___y_1473_ = v___y_1594_;
                    v___y_1474_ = v___y_1595_;
                    v___y_1475_ = v___y_1596_;
                    v___y_1476_ = v___y_1597_;
                    v___y_1477_ = v___y_1598_;
                    v___y_1478_ = v___y_1599_;
                    v___y_1479_ = v___y_1600_;
                    v___y_1480_ = v___y_1603_;
                    v___y_1481_ = v___y_1602_;
                    v___y_1482_ = v___y_1604_;
                    v___y_1483_ = v___x_1607_;
                    v___y_1484_ = v___x_1609_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1601_);
                    v___x_1610_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29;
                    v___y_1456_ = v___y_1577_;
                    v___y_1457_ = v___y_1578_;
                    v___y_1458_ = v___y_1580_;
                    v___y_1459_ = v___y_1579_;
                    v___y_1460_ = v___y_1581_;
                    v___y_1461_ = v___y_1582_;
                    v___y_1462_ = v___y_1583_;
                    v___y_1463_ = v___y_1584_;
                    v___y_1464_ = v___y_1585_;
                    v___y_1465_ = v___y_1586_;
                    v___y_1466_ = v___y_1587_;
                    v___y_1467_ = v___y_1588_;
                    v___y_1468_ = v___y_1589_;
                    v___y_1469_ = v___y_1590_;
                    v___y_1470_ = v___y_1591_;
                    v___y_1471_ = v___y_1592_;
                    v___y_1472_ = v___y_1593_;
                    v___y_1473_ = v___y_1594_;
                    v___y_1474_ = v___y_1595_;
                    v___y_1475_ = v___y_1596_;
                    v___y_1476_ = v___y_1597_;
                    v___y_1477_ = v___y_1598_;
                    v___y_1478_ = v___y_1599_;
                    v___y_1479_ = v___y_1600_;
                    v___y_1480_ = v___y_1603_;
                    v___y_1481_ = v___y_1602_;
                    v___y_1482_ = v___y_1604_;
                    v___y_1483_ = v___x_1607_;
                    v___y_1484_ = v___x_1610_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_quotContext_1621_ = leanh::lean_ctor_get(v_a_1443_, 1);
                v_currMacroScope_1622_ = leanh::lean_ctor_get(v_a_1443_, 2);
                v_ref_1623_ = leanh::lean_ctor_get(v_a_1443_, 5);
                v___x_1624_ = l_Lean_mkIdentFrom(v_id_1454_, v___y_1620_, v___y_1616_);
                leanh::lean_inc_ref(v___y_1619_);
                leanh::lean_inc(v___y_1615_);
                v___x_1625_ = l_Lean_Syntax_mkApp(v___y_1615_, v___y_1619_);
                v___x_1626_ = l_Lean_SourceInfo_fromRef(v_ref_1623_, v___y_1616_);
                v___x_1627_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31;
                v___x_1628_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32;
                v___x_1629_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33;
                v___x_1630_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34;
                v___x_1631_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36;
                v___x_1632_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38;
                v___x_1633_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39);
                leanh::lean_inc_n(v___x_1626_, 19);
                v___x_1634_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1634_, 0, v___x_1626_);
                leanh::lean_ctor_set(v___x_1634_, 1, v___x_1627_);
                leanh::lean_ctor_set(v___x_1634_, 2, v___x_1633_);
                v___x_1635_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40;
                v___x_1636_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41;
                v___x_1637_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1637_, 0, v___x_1626_);
                leanh::lean_ctor_set(v___x_1637_, 1, v___x_1635_);
                v___x_1638_ = l_Lean_Syntax_node1(v___x_1626_, v___x_1636_, v___x_1637_);
                v___x_1639_ = l_Lean_Syntax_node1(v___x_1626_, v___x_1627_, v___x_1638_);
                leanh::lean_inc_ref_n(v___x_1634_, 7);
                v___x_1640_ = l_Lean_Syntax_node7(
                    v___x_1626_,
                    v___x_1632_,
                    v___x_1634_,
                    v___x_1634_,
                    v___x_1639_,
                    v___x_1634_,
                    v___x_1634_,
                    v___x_1634_,
                    v___x_1634_,
                );
                v___x_1641_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42;
                v___x_1642_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43;
                v___x_1643_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1643_, 0, v___x_1626_);
                leanh::lean_ctor_set(v___x_1643_, 1, v___x_1641_);
                v___x_1644_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45;
                v___x_1645_ = leanh::lean_box(2);
                v___x_1646_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47;
                v___x_1647_ = leanh::lean_unsigned_to_nat(2);
                v___x_1648_ = lean_mk_empty_array_with_capacity(v___x_1647_);
                leanh::lean_inc_ref(v___x_1648_);
                v___x_1649_ = lean_array_push(v___x_1648_, v___y_1615_);
                v___x_1650_ = lean_array_push(v___x_1649_, v___x_1646_);
                v___x_1651_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1651_, 0, v___x_1645_);
                leanh::lean_ctor_set(v___x_1651_, 1, v___x_1644_);
                leanh::lean_ctor_set(v___x_1651_, 2, v___x_1650_);
                v___x_1652_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49;
                v_sz_1653_ = lean_array_size(v___y_1612_);
                v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1(v_sz_1653_, v___y_1614_, v___y_1612_);
                v___x_1655_ = l_Array_append___redArg(v___x_1633_, v___x_1654_);
                leanh::lean_dec_ref(v___x_1654_);
                v___x_1656_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1656_, 0, v___x_1626_);
                leanh::lean_ctor_set(v___x_1656_, 1, v___x_1627_);
                leanh::lean_ctor_set(v___x_1656_, 2, v___x_1655_);
                v___x_1657_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50;
                v___x_1658_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52;
                v___x_1659_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53;
                v___x_1660_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1660_, 0, v___x_1626_);
                leanh::lean_ctor_set(v___x_1660_, 1, v___x_1659_);
                v___x_1661_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55;
                v___x_1662_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57);
                v___x_1663_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58;
                leanh::lean_inc(v_currMacroScope_1622_);
                leanh::lean_inc(v_quotContext_1621_);
                v___x_1664_ =
                    l_Lean_addMacroScope(v_quotContext_1621_, v___x_1663_, v_currMacroScope_1622_);
                v___x_1665_ = leanh::lean_box(0);
                v___x_1666_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62;
                v___x_1667_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1667_, 0, v___x_1626_);
                leanh::lean_ctor_set(v___x_1667_, 1, v___x_1662_);
                leanh::lean_ctor_set(v___x_1667_, 2, v___x_1664_);
                leanh::lean_ctor_set(v___x_1667_, 3, v___x_1666_);
                v___x_1668_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63;
                v___x_1669_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1669_, 0, v___x_1626_);
                leanh::lean_ctor_set(v___x_1669_, 1, v___x_1668_);
                v___x_1670_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65;
                v___x_1671_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66;
                v___x_1672_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1672_, 0, v___x_1626_);
                leanh::lean_ctor_set(v___x_1672_, 1, v___x_1671_);
                v___x_1673_ = l_Lean_Syntax_node1(v___x_1626_, v___x_1670_, v___x_1672_);
                v___x_1674_ = l_Lean_Syntax_node1(v___x_1626_, v___x_1627_, v___x_1673_);
                v___x_1675_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67;
                v___x_1676_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1676_, 0, v___x_1626_);
                leanh::lean_ctor_set(v___x_1676_, 1, v___x_1675_);
                v___x_1677_ = l_Lean_Syntax_node4(
                    v___x_1626_,
                    v___x_1661_,
                    v___x_1667_,
                    v___x_1669_,
                    v___x_1674_,
                    v___x_1676_,
                );
                leanh::lean_inc_ref(v___x_1660_);
                v___x_1678_ =
                    l_Lean_Syntax_node2(v___x_1626_, v___x_1658_, v___x_1660_, v___x_1677_);
                leanh::lean_inc_ref(v___x_1656_);
                v___x_1679_ =
                    l_Lean_Syntax_node2(v___x_1626_, v___x_1652_, v___x_1656_, v___x_1678_);
                v___x_1680_ = l_Lean_Syntax_node4(
                    v___x_1626_,
                    v___x_1642_,
                    v___x_1643_,
                    v___x_1651_,
                    v___x_1679_,
                    v___x_1634_,
                );
                v___x_1681_ =
                    l_Lean_Syntax_node2(v___x_1626_, v___x_1631_, v___x_1640_, v___x_1680_);
                if leanh::lean_obj_tag(v___y_1617_) == 1 {
                    v_val_1682_ = leanh::lean_ctor_get(v___y_1617_, 0);
                    leanh::lean_inc(v_val_1682_);
                    leanh::lean_dec_ref_known(v___y_1617_, 1);
                    v___x_1683_ = l_Array_mkArray1___redArg(v_val_1682_);
                    leanh::lean_inc(v_quotContext_1621_);
                    leanh::lean_inc(v_currMacroScope_1622_);
                    v___y_1577_ = v___x_1681_;
                    v___y_1578_ = v___x_1629_;
                    v___y_1579_ = v_currMacroScope_1622_;
                    v___y_1580_ = v___x_1633_;
                    v___y_1581_ = v___x_1665_;
                    v___y_1582_ = v___x_1630_;
                    v___y_1583_ = v___x_1632_;
                    v___y_1584_ = v___x_1648_;
                    v___y_1585_ = v___x_1657_;
                    v___y_1586_ = v___x_1625_;
                    v___y_1587_ = v___x_1645_;
                    v___y_1588_ = v___x_1624_;
                    v___y_1589_ = v___y_1618_;
                    v___y_1590_ = v_quotContext_1621_;
                    v___y_1591_ = v___x_1627_;
                    v___y_1592_ = v___x_1656_;
                    v___y_1593_ = v___x_1634_;
                    v___y_1594_ = v___x_1644_;
                    v___y_1595_ = v___y_1619_;
                    v___y_1596_ = v___x_1626_;
                    v___y_1597_ = v___x_1631_;
                    v___y_1598_ = v___x_1665_;
                    v___y_1599_ = v___x_1658_;
                    v___y_1600_ = v___x_1628_;
                    v___y_1601_ = v___y_1613_;
                    v___y_1602_ = v___x_1660_;
                    v___y_1603_ = v___x_1646_;
                    v___y_1604_ = v___x_1652_;
                    v___y_1605_ = v___x_1683_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1617_);
                    v___x_1684_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29;
                    leanh::lean_inc(v_quotContext_1621_);
                    leanh::lean_inc(v_currMacroScope_1622_);
                    v___y_1577_ = v___x_1681_;
                    v___y_1578_ = v___x_1629_;
                    v___y_1579_ = v_currMacroScope_1622_;
                    v___y_1580_ = v___x_1633_;
                    v___y_1581_ = v___x_1665_;
                    v___y_1582_ = v___x_1630_;
                    v___y_1583_ = v___x_1632_;
                    v___y_1584_ = v___x_1648_;
                    v___y_1585_ = v___x_1657_;
                    v___y_1586_ = v___x_1625_;
                    v___y_1587_ = v___x_1645_;
                    v___y_1588_ = v___x_1624_;
                    v___y_1589_ = v___y_1618_;
                    v___y_1590_ = v_quotContext_1621_;
                    v___y_1591_ = v___x_1627_;
                    v___y_1592_ = v___x_1656_;
                    v___y_1593_ = v___x_1634_;
                    v___y_1594_ = v___x_1644_;
                    v___y_1595_ = v___y_1619_;
                    v___y_1596_ = v___x_1626_;
                    v___y_1597_ = v___x_1631_;
                    v___y_1598_ = v___x_1665_;
                    v___y_1599_ = v___x_1658_;
                    v___y_1600_ = v___x_1628_;
                    v___y_1601_ = v___y_1613_;
                    v___y_1602_ = v___x_1660_;
                    v___y_1603_ = v___x_1646_;
                    v___y_1604_ = v___x_1652_;
                    v___y_1605_ = v___x_1684_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_1694_ = 0;
                v___x_1695_ = l_Lean_mkIdentFrom(v_id_1454_, v___y_1693_, v___x_1694_);
                v___x_1696_ = l_Lean_Name_hasMacroScopes(v___y_1692_);
                if v___x_1696_ == 0 {
                    v___x_1697_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1(v___y_1692_);
                    v___y_1612_ = v___y_1686_;
                    v___y_1613_ = v___y_1688_;
                    v___y_1614_ = v___y_1687_;
                    v___y_1615_ = v___x_1695_;
                    v___y_1616_ = v___x_1694_;
                    v___y_1617_ = v___y_1691_;
                    v___y_1618_ = v___y_1690_;
                    v___y_1619_ = v___y_1689_;
                    v___y_1620_ = v___x_1697_;
                    state = 3;
                    continue;
                } else {
                    v_view_1698_ = l_Lean_extractMacroScopes(v___y_1692_);
                    v_name_1699_ = leanh::lean_ctor_get(v_view_1698_, 0);
                    v_imported_1700_ = leanh::lean_ctor_get(v_view_1698_, 1);
                    v_ctx_1701_ = leanh::lean_ctor_get(v_view_1698_, 2);
                    v_scopes_1702_ = leanh::lean_ctor_get(v_view_1698_, 3);
                    v_isSharedCheck_1711_ = (!leanh::lean_is_exclusive(v_view_1698_)) as u8;
                    if v_isSharedCheck_1711_ == 0 {
                        v___x_1704_ = v_view_1698_;
                        v_isShared_1705_ = v_isSharedCheck_1711_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_scopes_1702_);
                        leanh::lean_inc(v_ctx_1701_);
                        leanh::lean_inc(v_imported_1700_);
                        leanh::lean_inc(v_name_1699_);
                        leanh::lean_dec(v_view_1698_);
                        v___x_1704_ = leanh::lean_box(0);
                        v_isShared_1705_ = v_isSharedCheck_1711_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1706_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1(v_name_1699_);
                if v_isShared_1705_ == 0 {
                    leanh::lean_ctor_set(v___x_1704_, 0, v___x_1706_);
                    v___x_1708_ = v___x_1704_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_imported_1700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_ctx_1701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_scopes_1702_);
                    v___x_1708_ = v_reuseFailAlloc_1710_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1709_ = l_Lean_MacroScopesView_review(v___x_1708_);
                v___y_1612_ = v___y_1686_;
                v___y_1613_ = v___y_1688_;
                v___y_1614_ = v___y_1687_;
                v___y_1615_ = v___x_1695_;
                v___y_1616_ = v___x_1694_;
                v___y_1617_ = v___y_1691_;
                v___y_1618_ = v___y_1690_;
                v___y_1619_ = v___y_1689_;
                v___y_1620_ = v___x_1709_;
                state = 3;
                continue;
            }
            7 => {
                v___x_1718_ = l_Lake_expandBinders(v_bs_1714_, v_a_1443_, v_a_1444_);
                leanh::lean_dec_ref(v_bs_1714_);
                if leanh::lean_obj_tag(v___x_1718_) == 0 {
                    v_a_1719_ = leanh::lean_ctor_get(v___x_1718_, 0);
                    leanh::lean_inc(v_a_1719_);
                    v_a_1720_ = leanh::lean_ctor_get(v___x_1718_, 1);
                    leanh::lean_inc(v_a_1720_);
                    leanh::lean_dec_ref_known(v___x_1718_, 2);
                    v_sz_1721_ = lean_array_size(v_a_1719_);
                    v___x_1722_ = 0usize;
                    v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0(v_sz_1721_, v___x_1722_, v_a_1719_);
                    v___x_1724_ = l_Array_unzip___redArg(v___x_1723_);
                    leanh::lean_dec_ref(v___x_1723_);
                    v_fst_1725_ = leanh::lean_ctor_get(v___x_1724_, 0);
                    leanh::lean_inc(v_fst_1725_);
                    v_snd_1726_ = leanh::lean_ctor_get(v___x_1724_, 1);
                    leanh::lean_inc(v_snd_1726_);
                    leanh::lean_dec_ref(v___x_1724_);
                    v___x_1727_ = l_Lean_TSyntax_getId(v_id_1454_);
                    v___x_1728_ = l_Lean_Name_hasMacroScopes(v___x_1727_);
                    if v___x_1728_ == 0 {
                        leanh::lean_inc(v___x_1727_);
                        v___x_1729_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0(v___x_1727_);
                        v___y_1686_ = v_fst_1725_;
                        v___y_1687_ = v___x_1722_;
                        v___y_1688_ = v___y_1716_;
                        v___y_1689_ = v_snd_1726_;
                        v___y_1690_ = v_a_1720_;
                        v___y_1691_ = v___y_1717_;
                        v___y_1692_ = v___x_1727_;
                        v___y_1693_ = v___x_1729_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_1727_);
                        v_view_1730_ = l_Lean_extractMacroScopes(v___x_1727_);
                        v_name_1731_ = leanh::lean_ctor_get(v_view_1730_, 0);
                        v_imported_1732_ = leanh::lean_ctor_get(v_view_1730_, 1);
                        v_ctx_1733_ = leanh::lean_ctor_get(v_view_1730_, 2);
                        v_scopes_1734_ = leanh::lean_ctor_get(v_view_1730_, 3);
                        v_isSharedCheck_1743_ =
                            (!leanh::lean_is_exclusive(v_view_1730_)) as u8;
                        if v_isSharedCheck_1743_ == 0 {
                            v___x_1736_ = v_view_1730_;
                            v_isShared_1737_ = v_isSharedCheck_1743_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_scopes_1734_);
                            leanh::lean_inc(v_ctx_1733_);
                            leanh::lean_inc(v_imported_1732_);
                            leanh::lean_inc(v_name_1731_);
                            leanh::lean_dec(v_view_1730_);
                            v___x_1736_ = leanh::lean_box(0);
                            v_isShared_1737_ = v_isSharedCheck_1743_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_1717_);
                    leanh::lean_dec(v___y_1716_);
                    leanh::lean_dec(v_id_1454_);
                    v_a_1744_ = leanh::lean_ctor_get(v___x_1718_, 0);
                    v_a_1745_ = leanh::lean_ctor_get(v___x_1718_, 1);
                    v_isSharedCheck_1752_ = (!leanh::lean_is_exclusive(v___x_1718_)) as u8;
                    if v_isSharedCheck_1752_ == 0 {
                        v___x_1747_ = v___x_1718_;
                        v_isShared_1748_ = v_isSharedCheck_1752_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1745_);
                        leanh::lean_inc(v_a_1744_);
                        leanh::lean_dec(v___x_1718_);
                        v___x_1747_ = leanh::lean_box(0);
                        v_isShared_1748_ = v_isSharedCheck_1752_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1738_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0(v_name_1731_);
                if v_isShared_1737_ == 0 {
                    leanh::lean_ctor_set(v___x_1736_, 0, v___x_1738_);
                    v___x_1740_ = v___x_1736_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_imported_1732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_ctx_1733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_scopes_1734_);
                    v___x_1740_ = v_reuseFailAlloc_1742_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1741_ = l_Lean_MacroScopesView_review(v___x_1740_);
                v___y_1686_ = v_fst_1725_;
                v___y_1687_ = v___x_1722_;
                v___y_1688_ = v___y_1716_;
                v___y_1689_ = v_snd_1726_;
                v___y_1690_ = v_a_1720_;
                v___y_1691_ = v___y_1717_;
                v___y_1692_ = v___x_1727_;
                v___y_1693_ = v___x_1741_;
                state = 4;
                continue;
            }
            10 => {
                if v_isShared_1748_ == 0 {
                    v___x_1750_ = v___x_1747_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1751_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1744_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_a_1745_);
                    v___x_1750_ = v_reuseFailAlloc_1751_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1750_;
            }
            12 => {
                v___x_1755_ = l_Lean_Syntax_getOptional_x3f(v___x_1450_);
                leanh::lean_dec(v___x_1450_);
                if leanh::lean_obj_tag(v___x_1755_) == 0 {
                    v___x_1756_ = leanh::lean_box(0);
                    v___y_1716_ = v___y_1754_;
                    v___y_1717_ = v___x_1756_;
                    state = 7;
                    continue;
                } else {
                    v_val_1757_ = leanh::lean_ctor_get(v___x_1755_, 0);
                    v_isSharedCheck_1764_ = (!leanh::lean_is_exclusive(v___x_1755_)) as u8;
                    if v_isSharedCheck_1764_ == 0 {
                        v___x_1759_ = v___x_1755_;
                        v_isShared_1760_ = v_isSharedCheck_1764_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1757_);
                        leanh::lean_dec(v___x_1755_);
                        v___x_1759_ = leanh::lean_box(0);
                        v_isShared_1760_ = v_isSharedCheck_1764_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_1760_ == 0 {
                    v___x_1762_ = v___x_1759_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_val_1757_);
                    v___x_1762_ = v_reuseFailAlloc_1763_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_1716_ = v___y_1754_;
                v___y_1717_ = v___x_1762_;
                state = 7;
                continue;
            }
            15 => {
                if v_isShared_1770_ == 0 {
                    v___x_1772_ = v___x_1769_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1773_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_val_1767_);
                    v___x_1772_ = v_reuseFailAlloc_1773_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___y_1754_ = v___x_1772_;
                state = 12;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___boxed(
    mut v_x_1775_: *mut leanh::LeanObject,
    mut v_a_1776_: *mut leanh::LeanObject,
    mut v_a_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1778_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1(
        v_x_1775_, v_a_1776_, v_a_1777_,
    );
    leanh::lean_dec_ref(v_a_1776_);
    return v_res_1778_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0(
    mut v_sz_1810_: usize,
    mut v_i_1811_: usize,
    mut v_bs_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1813_: u8 = 0;
    let mut v_v_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: usize = 0;
    let mut v___x_1818_: usize = 0;
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1813_ = lean_usize_dec_lt(v_i_1811_, v_sz_1810_);
                if v___x_1813_ == 0 {
                    return v_bs_1812_;
                } else {
                    v_v_1814_ = lean_array_uget(v_bs_1812_, v_i_1811_);
                    v___x_1815_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1816_ = lean_array_uset(v_bs_1812_, v_i_1811_, v___x_1815_);
                    v___x_1817_ = 1usize;
                    v___x_1818_ = lean_usize_add(v_i_1811_, v___x_1817_);
                    v___x_1819_ = lean_array_uset(v_bs_x27_1816_, v_i_1811_, v_v_1814_);
                    v_i_1811_ = v___x_1818_;
                    v_bs_1812_ = v___x_1819_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0___boxed(
    mut v_sz_1821_: *mut leanh::LeanObject,
    mut v_i_1822_: *mut leanh::LeanObject,
    mut v_bs_1823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1824_: usize = 0;
    let mut v_i_boxed_1825_: usize = 0;
    let mut v_res_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1824_ = leanh::lean_unbox_usize(v_sz_1821_);
    leanh::lean_dec(v_sz_1821_);
    v_i_boxed_1825_ = leanh::lean_unbox_usize(v_i_1822_);
    leanh::lean_dec(v_i_1822_);
    v_res_1826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0(v_sz_boxed_1824_, v_i_boxed_1825_, v_bs_1823_);
    return v_res_1826_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1(
    mut v_sz_1827_: usize,
    mut v_i_1828_: usize,
    mut v_bs_1829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1830_: u8 = 0;
    let mut v_v_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: usize = 0;
    let mut v___x_1835_: usize = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1830_ = lean_usize_dec_lt(v_i_1828_, v_sz_1827_);
                if v___x_1830_ == 0 {
                    return v_bs_1829_;
                } else {
                    v_v_1831_ = lean_array_uget(v_bs_1829_, v_i_1828_);
                    v___x_1832_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1833_ = lean_array_uset(v_bs_1829_, v_i_1828_, v___x_1832_);
                    v___x_1834_ = 1usize;
                    v___x_1835_ = lean_usize_add(v_i_1828_, v___x_1834_);
                    v___x_1836_ = lean_array_uset(v_bs_x27_1833_, v_i_1828_, v_v_1831_);
                    v_i_1828_ = v___x_1835_;
                    v_bs_1829_ = v___x_1836_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1___boxed(
    mut v_sz_1838_: *mut leanh::LeanObject,
    mut v_i_1839_: *mut leanh::LeanObject,
    mut v_bs_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1841_: usize = 0;
    let mut v_i_boxed_1842_: usize = 0;
    let mut v_res_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1841_ = leanh::lean_unbox_usize(v_sz_1838_);
    leanh::lean_dec(v_sz_1838_);
    v_i_boxed_1842_ = leanh::lean_unbox_usize(v_i_1839_);
    leanh::lean_dec(v_i_1839_);
    v_res_1843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1(v_sz_boxed_1841_, v_i_boxed_1842_, v_bs_1840_);
    return v_res_1843_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2(
    mut v___x_1851_: *mut leanh::LeanObject,
    mut v___x_1852_: *mut leanh::LeanObject,
    mut v_sz_1853_: usize,
    mut v_i_1854_: usize,
    mut v_bs_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: usize = 0;
    let mut v___x_1869_: usize = 0;
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1856_ = lean_usize_dec_lt(v_i_1854_, v_sz_1853_);
                if v___x_1856_ == 0 {
                    leanh::lean_dec(v___x_1852_);
                    leanh::lean_dec(v___x_1851_);
                    return v_bs_1855_;
                } else {
                    v___x_1857_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31;
                    v_v_1858_ = lean_array_uget(v_bs_1855_, v_i_1854_);
                    v___x_1859_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1860_ = lean_array_uset(v_bs_1855_, v_i_1854_, v___x_1859_);
                    v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1;
                    v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2;
                    leanh::lean_inc_n(v___x_1851_, 4);
                    v___x_1863_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1863_, 0, v___x_1851_);
                    leanh::lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                    v___x_1864_ = l_Lean_Syntax_node1(v___x_1851_, v___x_1857_, v_v_1858_);
                    v___x_1865_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67;
                    v___x_1866_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1866_, 0, v___x_1851_);
                    leanh::lean_ctor_set(v___x_1866_, 1, v___x_1865_);
                    leanh::lean_inc(v___x_1852_);
                    v___x_1867_ = l_Lean_Syntax_node4(
                        v___x_1851_,
                        v___x_1861_,
                        v___x_1863_,
                        v___x_1864_,
                        v___x_1852_,
                        v___x_1866_,
                    );
                    v___x_1868_ = 1usize;
                    v___x_1869_ = lean_usize_add(v_i_1854_, v___x_1868_);
                    v___x_1870_ = lean_array_uset(v_bs_x27_1860_, v_i_1854_, v___x_1867_);
                    v_i_1854_ = v___x_1869_;
                    v_bs_1855_ = v___x_1870_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___boxed(
    mut v___x_1872_: *mut leanh::LeanObject,
    mut v___x_1873_: *mut leanh::LeanObject,
    mut v_sz_1874_: *mut leanh::LeanObject,
    mut v_i_1875_: *mut leanh::LeanObject,
    mut v_bs_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1877_: usize = 0;
    let mut v_i_boxed_1878_: usize = 0;
    let mut v_res_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1877_ = leanh::lean_unbox_usize(v_sz_1874_);
    leanh::lean_dec(v_sz_1874_);
    v_i_boxed_1878_ = leanh::lean_unbox_usize(v_i_1875_);
    leanh::lean_dec(v_i_1875_);
    v_res_1879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2(v___x_1872_, v___x_1873_, v_sz_boxed_1877_, v_i_boxed_1878_, v_bs_1876_);
    return v_res_1879_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1881_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0;
    v___x_1882_ = l_String_toRawSubstring_x27(v___x_1881_);
    return v___x_1882_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9;
    v___x_1895_ = l_String_toRawSubstring_x27(v___x_1894_);
    return v___x_1895_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19;
    v___x_1908_ = l_String_toRawSubstring_x27(v___x_1907_);
    return v___x_1908_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23;
    v___x_1915_ = l_String_toRawSubstring_x27(v___x_1914_);
    return v___x_1915_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mk_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30;
    v_mk_1928_ = lean_mk_syntax_ident(v___x_1927_);
    return v_mk_1928_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeMk_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33;
    v_unsafeMk_1933_ = lean_mk_syntax_ident(v___x_1932_);
    return v_unsafeMk_1933_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instCoeMk_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1937_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36;
    v_instCoeMk_1938_ = lean_mk_syntax_ident(v___x_1937_);
    return v_instCoeMk_1938_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39;
    v_get_1943_ = lean_mk_syntax_ident(v___x_1942_);
    return v_get_1943_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeGet_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1947_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42;
    v_unsafeGet_1948_ = lean_mk_syntax_ident(v___x_1947_);
    return v_unsafeGet_1948_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46()
-> *mut leanh::LeanObject {
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instCoeGet_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45;
    v_instCoeGet_1953_ = lean_mk_syntax_ident(v___x_1952_);
    return v_instCoeGet_1953_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59()
-> *mut leanh::LeanObject {
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1986_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58;
    v___x_1987_ = l_String_toRawSubstring_x27(v___x_1986_);
    return v___x_1987_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67()
-> *mut leanh::LeanObject {
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeMk_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2008_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47;
    v_unsafeMk_2009_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34);
    v___x_2010_ = leanh::lean_unsigned_to_nat(2);
    v___x_2011_ = lean_mk_empty_array_with_capacity(v___x_2010_);
    v___x_2012_ = lean_array_push(v___x_2011_, v_unsafeMk_2009_);
    v___x_2013_ = lean_array_push(v___x_2012_, v___x_2008_);
    return v___x_2013_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68()
-> *mut leanh::LeanObject {
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2014_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67);
    v___x_2015_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45;
    v___x_2016_ = leanh::lean_box(2);
    v___x_2017_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2017_, 0, v___x_2016_);
    leanh::lean_ctor_set(v___x_2017_, 1, v___x_2015_);
    leanh::lean_ctor_set(v___x_2017_, 2, v___x_2014_);
    return v___x_2017_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76()
-> *mut leanh::LeanObject {
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75;
    v___x_2042_ = l_String_toRawSubstring_x27(v___x_2041_);
    return v___x_2042_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82()
-> *mut leanh::LeanObject {
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81;
    v___x_2058_ = l_String_toRawSubstring_x27(v___x_2057_);
    return v___x_2058_;
}
pub unsafe fn l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1(
    mut v_x_2061_: *mut leanh::LeanObject,
    mut v_a_2062_: *mut leanh::LeanObject,
    mut v_a_2063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2078_: usize = 0;
    let mut v___y_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2121_: usize = 0;
    let mut v___y_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2215_: usize = 0;
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mk_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeMk_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instCoeMk_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeGet_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instCoeGet_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2358_: usize = 0;
    let mut v___x_2359_: usize = 0;
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2064_ = l_Lake_hydrateOpaqueTypeCmd___closed__1;
                leanh::lean_inc(v_x_2061_);
                v___x_2065_ = l_Lean_Syntax_isOfKind(v_x_2061_, v___x_2064_);
                if v___x_2065_ == 0 {
                    leanh::lean_dec(v_x_2061_);
                    v___x_2066_ = leanh::lean_box(1);
                    v___x_2067_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2067_, 0, v___x_2066_);
                    leanh::lean_ctor_set(v___x_2067_, 1, v_a_2063_);
                    return v___x_2067_;
                } else {
                    v___x_2068_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2069_ = l_Lean_Syntax_getArg(v_x_2061_, v___x_2068_);
                    v___x_2070_ = leanh::lean_unsigned_to_nat(2);
                    v___x_2071_ = l_Lean_Syntax_getArg(v_x_2061_, v___x_2070_);
                    v___x_2072_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2073_ = l_Lean_Syntax_getArg(v_x_2061_, v___x_2072_);
                    v___x_2074_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2075_ = l_Lean_Syntax_getArg(v_x_2061_, v___x_2074_);
                    leanh::lean_dec(v_x_2061_);
                    v_args_2076_ = l_Lean_Syntax_getArgs(v___x_2075_);
                    leanh::lean_dec(v___x_2075_);
                    v___x_2397_ = l_Lean_Syntax_getOptional_x3f(v___x_2069_);
                    leanh::lean_dec(v___x_2069_);
                    if leanh::lean_obj_tag(v___x_2397_) == 0 {
                        v___x_2398_ = leanh::lean_box(0);
                        v___y_2288_ = v___x_2398_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2399_ = leanh::lean_ctor_get(v___x_2397_, 0);
                        v_isSharedCheck_2406_ =
                            (!leanh::lean_is_exclusive(v___x_2397_)) as u8;
                        if v_isSharedCheck_2406_ == 0 {
                            v___x_2401_ = v___x_2397_;
                            v_isShared_2402_ = v_isSharedCheck_2406_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2399_);
                            leanh::lean_dec(v___x_2397_);
                            v___x_2401_ = leanh::lean_box(0);
                            v_isShared_2402_ = v_isSharedCheck_2406_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_2084_);
                v___x_2130_ = l_Array_append___redArg(v___y_2084_, v___y_2129_);
                leanh::lean_dec_ref(v___y_2129_);
                leanh::lean_inc_n(v___y_2122_, 18);
                leanh::lean_inc_n(v___y_2119_, 79);
                v___x_2131_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2131_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2131_, 1, v___y_2122_);
                leanh::lean_ctor_set(v___x_2131_, 2, v___x_2130_);
                leanh::lean_inc_ref_n(v___x_2131_, 2);
                leanh::lean_inc_n(v___y_2086_, 34);
                leanh::lean_inc_n(v___y_2118_, 2);
                v___x_2132_ = l_Lean_Syntax_node7(
                    v___y_2119_,
                    v___y_2118_,
                    v___y_2086_,
                    v___y_2103_,
                    v___x_2131_,
                    v___y_2086_,
                    v___y_2086_,
                    v___y_2086_,
                    v___y_2086_,
                );
                v___x_2133_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42;
                leanh::lean_inc_ref_n(v___y_2106_, 4);
                leanh::lean_inc_ref_n(v___y_2125_, 8);
                leanh::lean_inc_ref_n(v___y_2089_, 9);
                v___x_2134_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2106_, v___x_2133_);
                v___x_2135_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2135_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2135_, 1, v___x_2133_);
                leanh::lean_inc_n(v___y_2079_, 3);
                leanh::lean_inc_ref_n(v___y_2082_, 2);
                v___x_2136_ = lean_array_push(v___y_2082_, v___y_2079_);
                leanh::lean_inc_n(v___y_2096_, 3);
                v___x_2137_ = lean_array_push(v___x_2136_, v___y_2096_);
                leanh::lean_inc_n(v___y_2094_, 5);
                leanh::lean_inc_n(v___y_2110_, 3);
                v___x_2138_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2138_, 0, v___y_2110_);
                leanh::lean_ctor_set(v___x_2138_, 1, v___y_2094_);
                leanh::lean_ctor_set(v___x_2138_, 2, v___x_2137_);
                v___x_2139_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48;
                v___x_2140_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2106_, v___x_2139_);
                leanh::lean_inc_n(v___x_2140_, 4);
                v___x_2141_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2140_, v___y_2086_, v___y_2095_);
                leanh::lean_inc_ref(v___x_2135_);
                leanh::lean_inc(v___x_2134_);
                v___x_2142_ = l_Lean_Syntax_node4(
                    v___y_2119_,
                    v___x_2134_,
                    v___x_2135_,
                    v___x_2138_,
                    v___x_2141_,
                    v___y_2086_,
                );
                leanh::lean_inc_n(v___y_2126_, 5);
                v___x_2143_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2126_, v___x_2132_, v___x_2142_);
                v___x_2144_ = l_Lean_Syntax_node7(
                    v___y_2119_,
                    v___y_2118_,
                    v___y_2086_,
                    v___y_2086_,
                    v___x_2131_,
                    v___y_2086_,
                    v___y_2086_,
                    v___y_2086_,
                    v___y_2086_,
                );
                v___x_2145_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13;
                v___x_2146_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2106_, v___x_2145_);
                v___x_2147_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2147_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2147_, 1, v___x_2145_);
                leanh::lean_inc(v___y_2083_);
                v___x_2148_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2094_, v___y_2083_, v___y_2086_);
                v___x_2149_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2148_);
                v___x_2150_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1);
                v___x_2151_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2;
                leanh::lean_inc_n(v___y_2092_, 3);
                leanh::lean_inc_n(v___y_2105_, 3);
                v___x_2152_ = l_Lean_addMacroScope(v___y_2105_, v___x_2151_, v___y_2092_);
                leanh::lean_inc_n(v___y_2116_, 3);
                v___x_2153_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2153_, 0, v___x_2151_);
                leanh::lean_ctor_set(v___x_2153_, 1, v___y_2116_);
                v___x_2154_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3;
                leanh::lean_inc_n(v___y_2117_, 4);
                v___x_2155_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2155_, 0, v___x_2154_);
                leanh::lean_ctor_set(v___x_2155_, 1, v___y_2117_);
                v___x_2156_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2156_, 0, v___x_2153_);
                leanh::lean_ctor_set(v___x_2156_, 1, v___x_2155_);
                v___x_2157_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2157_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2157_, 1, v___x_2150_);
                leanh::lean_ctor_set(v___x_2157_, 2, v___x_2152_);
                leanh::lean_ctor_set(v___x_2157_, 3, v___x_2156_);
                v___x_2158_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4;
                leanh::lean_inc_ref_n(v___y_2111_, 4);
                v___x_2159_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2111_, v___x_2158_);
                v___x_2160_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5;
                v___x_2161_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2111_, v___x_2160_);
                v___x_2162_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6;
                v___x_2163_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2163_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2163_, 1, v___x_2162_);
                v___x_2164_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8;
                v___x_2165_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10);
                v___x_2166_ = leanh::lean_box(0);
                v___x_2167_ = l_Lean_addMacroScope(v___y_2105_, v___x_2166_, v___y_2092_);
                v___x_2168_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12;
                v___x_2169_ = l_Lean_Name_mkStr1(v___y_2089_);
                v___x_2170_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2170_, 0, v___x_2169_);
                v___x_2171_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2171_, 0, v___x_2170_);
                leanh::lean_ctor_set(v___x_2171_, 1, v___y_2117_);
                v___x_2172_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2172_, 0, v___x_2168_);
                leanh::lean_ctor_set(v___x_2172_, 1, v___x_2171_);
                v___x_2173_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2173_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2173_, 1, v___x_2165_);
                leanh::lean_ctor_set(v___x_2173_, 2, v___x_2167_);
                leanh::lean_ctor_set(v___x_2173_, 3, v___x_2172_);
                v___x_2174_ = l_Lean_Syntax_node1(v___y_2119_, v___x_2164_, v___x_2173_);
                v___x_2175_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2161_, v___x_2163_, v___x_2174_);
                v___x_2176_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13;
                v___x_2177_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2177_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2177_, 1, v___x_2176_);
                leanh::lean_inc_ref(v___x_2177_);
                leanh::lean_inc(v___y_2099_);
                leanh::lean_inc(v___x_2175_);
                leanh::lean_inc(v___x_2159_);
                v___x_2178_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___x_2159_,
                    v___x_2175_,
                    v___y_2099_,
                    v___x_2177_,
                );
                leanh::lean_inc(v___y_2102_);
                v___x_2179_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___x_2159_,
                    v___x_2175_,
                    v___y_2102_,
                    v___x_2177_,
                );
                leanh::lean_inc_n(v___x_2179_, 2);
                leanh::lean_inc_n(v___x_2178_, 2);
                v___x_2180_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2122_, v___x_2178_, v___x_2179_);
                leanh::lean_inc_ref(v___x_2157_);
                leanh::lean_inc_n(v___y_2104_, 4);
                v___x_2181_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2104_, v___x_2157_, v___x_2180_);
                leanh::lean_inc_n(v___y_2107_, 3);
                leanh::lean_inc_n(v___y_2101_, 3);
                v___x_2182_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2101_, v___y_2107_, v___x_2181_);
                v___x_2183_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2140_, v___y_2086_, v___x_2182_);
                v___x_2184_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14;
                v___x_2185_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2111_, v___x_2184_);
                v___x_2186_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15;
                v___x_2187_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2187_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2187_, 1, v___x_2186_);
                v___x_2188_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___y_2079_);
                v___x_2189_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16;
                v___x_2190_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2190_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2190_, 1, v___x_2189_);
                leanh::lean_inc_ref_n(v___x_2190_, 2);
                leanh::lean_inc_ref_n(v___x_2187_, 2);
                leanh::lean_inc_n(v___x_2185_, 2);
                v___x_2191_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___x_2185_,
                    v___x_2187_,
                    v___x_2188_,
                    v___x_2190_,
                );
                leanh::lean_inc_n(v___y_2114_, 2);
                leanh::lean_inc_n(v___y_2093_, 2);
                leanh::lean_inc_n(v___y_2123_, 2);
                v___x_2192_ = l_Lean_Syntax_node4(
                    v___y_2119_,
                    v___y_2123_,
                    v___y_2093_,
                    v___x_2191_,
                    v___y_2114_,
                    v___y_2086_,
                );
                leanh::lean_inc_ref_n(v___x_2147_, 2);
                leanh::lean_inc_n(v___y_2127_, 3);
                leanh::lean_inc_n(v___x_2146_, 2);
                v___x_2193_ = l_Lean_Syntax_node6(
                    v___y_2119_,
                    v___x_2146_,
                    v___y_2127_,
                    v___x_2147_,
                    v___y_2086_,
                    v___x_2149_,
                    v___x_2183_,
                    v___x_2192_,
                );
                leanh::lean_inc_n(v___x_2144_, 2);
                v___x_2194_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2126_, v___x_2144_, v___x_2193_);
                leanh::lean_inc_n(v___y_2124_, 2);
                v___x_2195_ = lean_array_push(v___y_2082_, v___y_2124_);
                v___x_2196_ = lean_array_push(v___x_2195_, v___y_2096_);
                v___x_2197_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2197_, 0, v___y_2110_);
                leanh::lean_ctor_set(v___x_2197_, 1, v___y_2094_);
                leanh::lean_ctor_set(v___x_2197_, 2, v___x_2196_);
                v___x_2198_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___y_2080_,
                    v___y_2102_,
                    v___y_2128_,
                    v___y_2099_,
                );
                v___x_2199_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2101_, v___y_2107_, v___x_2198_);
                leanh::lean_inc(v___x_2199_);
                v___x_2200_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2199_);
                v___x_2201_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2112_, v___y_2086_, v___x_2200_);
                v___x_2202_ = l_Lean_Syntax_node5(
                    v___y_2119_,
                    v___y_2108_,
                    v___y_2088_,
                    v___x_2197_,
                    v___x_2201_,
                    v___y_2115_,
                    v___y_2086_,
                );
                v___x_2203_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2126_, v___y_2087_, v___x_2202_);
                v___x_2204_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___y_2124_);
                v___x_2205_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2098_, v___y_2120_, v___x_2204_);
                v___x_2206_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2091_, v___y_2127_, v___x_2205_);
                v___x_2207_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2206_);
                leanh::lean_inc(v___y_2109_);
                v___x_2208_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___y_2081_,
                    v___y_2090_,
                    v___x_2207_,
                    v___y_2109_,
                );
                v___x_2209_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2208_);
                v___x_2210_ = l_Lean_Syntax_node7(
                    v___y_2119_,
                    v___y_2118_,
                    v___y_2086_,
                    v___x_2209_,
                    v___x_2131_,
                    v___y_2086_,
                    v___y_2086_,
                    v___y_2086_,
                    v___y_2086_,
                );
                leanh::lean_inc_n(v___y_2113_, 2);
                v___x_2211_ = lean_array_push(v___y_2082_, v___y_2113_);
                v___x_2212_ = lean_array_push(v___x_2211_, v___y_2096_);
                v___x_2213_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2213_, 0, v___y_2110_);
                leanh::lean_ctor_set(v___x_2213_, 1, v___y_2094_);
                leanh::lean_ctor_set(v___x_2213_, 2, v___x_2212_);
                v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1(v___y_2078_, v___y_2121_, v_args_2076_);
                v_sz_2215_ = lean_array_size(v___x_2214_);
                v___x_2216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2(v___y_2119_, v___y_2086_, v_sz_2215_, v___y_2121_, v___x_2214_);
                v___x_2217_ = l_Array_append___redArg(v___y_2084_, v___x_2216_);
                leanh::lean_dec_ref(v___x_2216_);
                v___x_2218_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2218_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2218_, 1, v___y_2122_);
                leanh::lean_ctor_set(v___x_2218_, 2, v___x_2217_);
                v___x_2219_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2140_, v___x_2218_, v___x_2199_);
                v___x_2220_ = l_Lean_Syntax_node4(
                    v___y_2119_,
                    v___x_2134_,
                    v___x_2135_,
                    v___x_2213_,
                    v___x_2219_,
                    v___y_2086_,
                );
                v___x_2221_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2126_, v___x_2210_, v___x_2220_);
                leanh::lean_inc(v___y_2100_);
                v___x_2222_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2094_, v___y_2100_, v___y_2086_);
                v___x_2223_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2222_);
                v___x_2224_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2122_, v___x_2179_, v___x_2178_);
                v___x_2225_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2104_, v___x_2157_, v___x_2224_);
                v___x_2226_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2101_, v___y_2107_, v___x_2225_);
                v___x_2227_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2140_, v___y_2086_, v___x_2226_);
                v___x_2228_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___y_2113_);
                v___x_2229_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___x_2185_,
                    v___x_2187_,
                    v___x_2228_,
                    v___x_2190_,
                );
                v___x_2230_ = l_Lean_Syntax_node4(
                    v___y_2119_,
                    v___y_2123_,
                    v___y_2093_,
                    v___x_2229_,
                    v___y_2114_,
                    v___y_2086_,
                );
                v___x_2231_ = l_Lean_Syntax_node6(
                    v___y_2119_,
                    v___x_2146_,
                    v___y_2127_,
                    v___x_2147_,
                    v___y_2086_,
                    v___x_2223_,
                    v___x_2227_,
                    v___x_2230_,
                );
                v___x_2232_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2126_, v___x_2144_, v___x_2231_);
                v___x_2233_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17;
                v___x_2234_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2111_, v___x_2233_);
                v___x_2235_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18;
                v___x_2236_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2236_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2236_, 1, v___x_2235_);
                v___x_2237_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20);
                v___x_2238_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21;
                v___x_2239_ = l_Lean_addMacroScope(v___y_2105_, v___x_2238_, v___y_2092_);
                v___x_2240_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2240_, 0, v___x_2238_);
                leanh::lean_ctor_set(v___x_2240_, 1, v___y_2116_);
                v___x_2241_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22;
                v___x_2242_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2242_, 0, v___x_2241_);
                leanh::lean_ctor_set(v___x_2242_, 1, v___y_2117_);
                v___x_2243_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2243_, 0, v___x_2240_);
                leanh::lean_ctor_set(v___x_2243_, 1, v___x_2242_);
                v___x_2244_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2244_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2244_, 1, v___x_2237_);
                leanh::lean_ctor_set(v___x_2244_, 2, v___x_2239_);
                leanh::lean_ctor_set(v___x_2244_, 3, v___x_2243_);
                v___x_2245_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2178_);
                leanh::lean_inc_ref(v___x_2244_);
                v___x_2246_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2104_, v___x_2244_, v___x_2245_);
                v___x_2247_ = l_Lean_Syntax_node4(
                    v___y_2119_,
                    v___x_2234_,
                    v___x_2236_,
                    v___y_2086_,
                    v___x_2246_,
                    v___y_2109_,
                );
                v___x_2248_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2247_);
                v___x_2249_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2179_);
                v___x_2250_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2104_, v___x_2244_, v___x_2249_);
                v___x_2251_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2101_, v___y_2107_, v___x_2250_);
                v___x_2252_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2140_, v___x_2248_, v___x_2251_);
                v___x_2253_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24);
                v___x_2254_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25;
                v___x_2255_ = l_Lean_addMacroScope(v___y_2105_, v___x_2254_, v___y_2092_);
                v___x_2256_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26;
                v___x_2257_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2257_, 0, v___x_2256_);
                leanh::lean_ctor_set(v___x_2257_, 1, v___y_2116_);
                v___x_2258_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27;
                v___x_2259_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2259_, 0, v___x_2258_);
                leanh::lean_ctor_set(v___x_2259_, 1, v___y_2117_);
                v___x_2260_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2260_, 0, v___x_2257_);
                leanh::lean_ctor_set(v___x_2260_, 1, v___x_2259_);
                v___x_2261_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2261_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2261_, 1, v___x_2253_);
                leanh::lean_ctor_set(v___x_2261_, 2, v___x_2255_);
                leanh::lean_ctor_set(v___x_2261_, 3, v___x_2260_);
                v___x_2262_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2261_);
                v___x_2263_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2104_, v___y_2079_, v___x_2262_);
                v___x_2264_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2263_);
                v___x_2265_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___x_2185_,
                    v___x_2187_,
                    v___x_2264_,
                    v___x_2190_,
                );
                v___x_2266_ = l_Lean_Syntax_node4(
                    v___y_2119_,
                    v___y_2123_,
                    v___y_2093_,
                    v___x_2265_,
                    v___y_2114_,
                    v___y_2086_,
                );
                v___x_2267_ = l_Lean_Syntax_node6(
                    v___y_2119_,
                    v___x_2146_,
                    v___y_2127_,
                    v___x_2147_,
                    v___y_2086_,
                    v___y_2086_,
                    v___x_2252_,
                    v___x_2266_,
                );
                v___x_2268_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2126_, v___x_2144_, v___x_2267_);
                v___x_2269_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28;
                v___x_2270_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2106_, v___x_2269_);
                v___x_2271_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2271_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2271_, 1, v___x_2269_);
                v___x_2272_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2122_, v___x_2071_, v___y_2086_);
                v___x_2273_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2270_, v___x_2271_, v___x_2272_);
                v___x_2274_ = leanh::lean_unsigned_to_nat(9);
                v___x_2275_ = lean_mk_empty_array_with_capacity(v___x_2274_);
                v___x_2276_ = lean_array_push(v___x_2275_, v___y_2097_);
                v___x_2277_ = lean_array_push(v___x_2276_, v___y_2085_);
                v___x_2278_ = lean_array_push(v___x_2277_, v___x_2143_);
                v___x_2279_ = lean_array_push(v___x_2278_, v___x_2194_);
                v___x_2280_ = lean_array_push(v___x_2279_, v___x_2203_);
                v___x_2281_ = lean_array_push(v___x_2280_, v___x_2221_);
                v___x_2282_ = lean_array_push(v___x_2281_, v___x_2232_);
                v___x_2283_ = lean_array_push(v___x_2282_, v___x_2268_);
                v___x_2284_ = lean_array_push(v___x_2283_, v___x_2273_);
                v___x_2285_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2285_, 0, v___y_2119_);
                leanh::lean_ctor_set(v___x_2285_, 1, v___y_2122_);
                leanh::lean_ctor_set(v___x_2285_, 2, v___x_2284_);
                v___x_2286_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2286_, 0, v___x_2285_);
                leanh::lean_ctor_set(v___x_2286_, 1, v_a_2063_);
                return v___x_2286_;
            }
            2 => {
                v_quotContext_2289_ = leanh::lean_ctor_get(v_a_2062_, 1);
                v_currMacroScope_2290_ = leanh::lean_ctor_get(v_a_2062_, 2);
                v_ref_2291_ = leanh::lean_ctor_get(v_a_2062_, 5);
                v_mk_2292_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31);
                v_unsafeMk_2293_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34);
                v_instCoeMk_2294_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37);
                v_get_2295_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40);
                v_unsafeGet_2296_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43);
                v_instCoeGet_2297_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46);
                v___x_2298_ = 0;
                v___x_2299_ = l_Lean_SourceInfo_fromRef(v_ref_2291_, v___x_2298_);
                v___x_2300_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31;
                v___x_2301_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32;
                v___x_2302_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33;
                v___x_2303_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34;
                v___x_2304_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47;
                v___x_2305_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48;
                leanh::lean_inc_n(v___x_2299_, 42);
                v___x_2306_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2306_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2306_, 1, v___x_2304_);
                leanh::lean_inc_n(v___x_2071_, 2);
                v___x_2307_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2305_, v___x_2306_, v___x_2071_);
                v___x_2308_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36;
                v___x_2309_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38;
                v___x_2310_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39);
                v___x_2311_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2311_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2311_, 1, v___x_2300_);
                leanh::lean_ctor_set(v___x_2311_, 2, v___x_2310_);
                v___x_2312_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50;
                v___x_2313_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50;
                v___x_2314_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51;
                v___x_2315_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2315_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                v___x_2316_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53;
                v___x_2317_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54;
                leanh::lean_inc_ref_n(v___x_2311_, 11);
                v___x_2318_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2317_, v___x_2311_);
                v___x_2319_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57;
                v___x_2320_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59);
                v___x_2321_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60;
                leanh::lean_inc_n(v_currMacroScope_2290_, 3);
                leanh::lean_inc_n(v_quotContext_2289_, 3);
                v___x_2322_ =
                    l_Lean_addMacroScope(v_quotContext_2289_, v___x_2321_, v_currMacroScope_2290_);
                v___x_2323_ = leanh::lean_box(0);
                v___x_2324_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62;
                v___x_2325_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2325_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2325_, 1, v___x_2320_);
                leanh::lean_ctor_set(v___x_2325_, 2, v___x_2322_);
                leanh::lean_ctor_set(v___x_2325_, 3, v___x_2324_);
                v___x_2326_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2319_, v___x_2325_, v___x_2311_);
                leanh::lean_inc_n(v___x_2318_, 2);
                v___x_2327_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2316_, v___x_2318_, v___x_2326_);
                v___x_2328_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v___x_2327_);
                v___x_2329_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63;
                v___x_2330_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2330_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2330_, 1, v___x_2329_);
                leanh::lean_inc_ref_n(v___x_2330_, 2);
                leanh::lean_inc_ref_n(v___x_2315_, 2);
                v___x_2331_ = l_Lean_Syntax_node3(
                    v___x_2299_,
                    v___x_2313_,
                    v___x_2315_,
                    v___x_2328_,
                    v___x_2330_,
                );
                v___x_2332_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v___x_2331_);
                v___x_2333_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40;
                v___x_2334_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41;
                v___x_2335_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2335_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2335_, 1, v___x_2333_);
                v___x_2336_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2334_, v___x_2335_);
                v___x_2337_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v___x_2336_);
                v___x_2338_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64;
                v___x_2339_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65;
                v___x_2340_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2340_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2340_, 1, v___x_2338_);
                v___x_2341_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2339_, v___x_2340_);
                v___x_2342_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v___x_2341_);
                v___x_2343_ = l_Lean_Syntax_node7(
                    v___x_2299_,
                    v___x_2309_,
                    v___x_2311_,
                    v___x_2332_,
                    v___x_2337_,
                    v___x_2311_,
                    v___x_2311_,
                    v___x_2342_,
                    v___x_2311_,
                );
                v___x_2344_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66;
                v___x_2345_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1;
                v___x_2346_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2346_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2346_, 1, v___x_2345_);
                v___x_2347_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45;
                v___x_2348_ = leanh::lean_box(2);
                v___x_2349_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47;
                v___x_2350_ = lean_mk_empty_array_with_capacity(v___x_2070_);
                v___x_2351_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68);
                v___x_2352_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69;
                v___x_2353_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52;
                v___x_2354_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53;
                v___x_2355_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2355_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2355_, 1, v___x_2354_);
                v___x_2356_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71;
                v___x_2357_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72;
                v_sz_2358_ = lean_array_size(v_args_2076_);
                v___x_2359_ = 0usize;
                leanh::lean_inc_ref(v_args_2076_);
                v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0(v_sz_2358_, v___x_2359_, v_args_2076_);
                v___x_2361_ = l_Array_append___redArg(v___x_2310_, v___x_2360_);
                leanh::lean_dec_ref(v___x_2360_);
                v___x_2362_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2362_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2362_, 1, v___x_2300_);
                leanh::lean_ctor_set(v___x_2362_, 2, v___x_2361_);
                leanh::lean_inc_ref(v___x_2362_);
                v___x_2363_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2357_, v___x_2073_, v___x_2362_);
                v___x_2364_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73;
                v___x_2365_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2365_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2365_, 1, v___x_2364_);
                v___x_2366_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2357_, v___x_2071_, v___x_2362_);
                leanh::lean_inc(v___x_2366_);
                leanh::lean_inc_ref(v___x_2365_);
                leanh::lean_inc(v___x_2363_);
                v___x_2367_ = l_Lean_Syntax_node3(
                    v___x_2299_,
                    v___x_2356_,
                    v___x_2363_,
                    v___x_2365_,
                    v___x_2366_,
                );
                leanh::lean_inc_ref(v___x_2355_);
                v___x_2368_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2353_, v___x_2355_, v___x_2367_);
                leanh::lean_inc(v___x_2368_);
                v___x_2369_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v___x_2368_);
                v___x_2370_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2352_, v___x_2311_, v___x_2369_);
                v___x_2371_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74;
                v___x_2372_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6;
                v___x_2373_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2373_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2373_, 1, v___x_2372_);
                v___x_2374_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76);
                v___x_2375_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77;
                v___x_2376_ =
                    l_Lean_addMacroScope(v_quotContext_2289_, v___x_2375_, v_currMacroScope_2290_);
                v___x_2377_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79;
                v___x_2378_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2378_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2378_, 1, v___x_2374_);
                leanh::lean_ctor_set(v___x_2378_, 2, v___x_2376_);
                leanh::lean_ctor_set(v___x_2378_, 3, v___x_2377_);
                v___x_2379_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80;
                v___x_2380_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2379_, v___x_2311_, v___x_2311_);
                leanh::lean_inc(v___x_2380_);
                leanh::lean_inc_ref(v___x_2373_);
                v___x_2381_ = l_Lean_Syntax_node4(
                    v___x_2299_,
                    v___x_2371_,
                    v___x_2373_,
                    v___x_2378_,
                    v___x_2380_,
                    v___x_2311_,
                );
                leanh::lean_inc(v___x_2381_);
                leanh::lean_inc_ref(v___x_2346_);
                v___x_2382_ = l_Lean_Syntax_node5(
                    v___x_2299_,
                    v___x_2344_,
                    v___x_2346_,
                    v___x_2351_,
                    v___x_2370_,
                    v___x_2381_,
                    v___x_2311_,
                );
                leanh::lean_inc(v___x_2343_);
                v___x_2383_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2308_, v___x_2343_, v___x_2382_);
                v___x_2384_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82);
                v___x_2385_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83;
                v___x_2386_ =
                    l_Lean_addMacroScope(v_quotContext_2289_, v___x_2385_, v_currMacroScope_2290_);
                v___x_2387_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2387_, 0, v___x_2299_);
                leanh::lean_ctor_set(v___x_2387_, 1, v___x_2384_);
                leanh::lean_ctor_set(v___x_2387_, 2, v___x_2386_);
                leanh::lean_ctor_set(v___x_2387_, 3, v___x_2323_);
                v___x_2388_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v_unsafeMk_2293_);
                leanh::lean_inc_ref(v___x_2387_);
                v___x_2389_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2319_, v___x_2387_, v___x_2388_);
                v___x_2390_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2316_, v___x_2318_, v___x_2389_);
                v___x_2391_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v___x_2390_);
                v___x_2392_ = l_Lean_Syntax_node3(
                    v___x_2299_,
                    v___x_2313_,
                    v___x_2315_,
                    v___x_2391_,
                    v___x_2330_,
                );
                v___x_2393_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v___x_2392_);
                if leanh::lean_obj_tag(v___y_2288_) == 1 {
                    v_val_2394_ = leanh::lean_ctor_get(v___y_2288_, 0);
                    leanh::lean_inc(v_val_2394_);
                    leanh::lean_dec_ref_known(v___y_2288_, 1);
                    v___x_2395_ = l_Array_mkArray1___redArg(v_val_2394_);
                    leanh::lean_inc(v_quotContext_2289_);
                    leanh::lean_inc(v_currMacroScope_2290_);
                    v___y_2078_ = v_sz_2358_;
                    v___y_2079_ = v_mk_2292_;
                    v___y_2080_ = v___x_2356_;
                    v___y_2081_ = v___x_2313_;
                    v___y_2082_ = v___x_2350_;
                    v___y_2083_ = v_instCoeMk_2294_;
                    v___y_2084_ = v___x_2310_;
                    v___y_2085_ = v___x_2383_;
                    v___y_2086_ = v___x_2311_;
                    v___y_2087_ = v___x_2343_;
                    v___y_2088_ = v___x_2346_;
                    v___y_2089_ = v___x_2301_;
                    v___y_2090_ = v___x_2315_;
                    v___y_2091_ = v___x_2316_;
                    v___y_2092_ = v_currMacroScope_2290_;
                    v___y_2093_ = v___x_2373_;
                    v___y_2094_ = v___x_2347_;
                    v___y_2095_ = v___x_2368_;
                    v___y_2096_ = v___x_2349_;
                    v___y_2097_ = v___x_2307_;
                    v___y_2098_ = v___x_2319_;
                    v___y_2099_ = v___x_2363_;
                    v___y_2100_ = v_instCoeGet_2297_;
                    v___y_2101_ = v___x_2353_;
                    v___y_2102_ = v___x_2366_;
                    v___y_2103_ = v___x_2393_;
                    v___y_2104_ = v___x_2357_;
                    v___y_2105_ = v_quotContext_2289_;
                    v___y_2106_ = v___x_2303_;
                    v___y_2107_ = v___x_2355_;
                    v___y_2108_ = v___x_2344_;
                    v___y_2109_ = v___x_2330_;
                    v___y_2110_ = v___x_2348_;
                    v___y_2111_ = v___x_2312_;
                    v___y_2112_ = v___x_2352_;
                    v___y_2113_ = v_get_2295_;
                    v___y_2114_ = v___x_2380_;
                    v___y_2115_ = v___x_2381_;
                    v___y_2116_ = v___x_2323_;
                    v___y_2117_ = v___x_2323_;
                    v___y_2118_ = v___x_2309_;
                    v___y_2119_ = v___x_2299_;
                    v___y_2120_ = v___x_2387_;
                    v___y_2121_ = v___x_2359_;
                    v___y_2122_ = v___x_2300_;
                    v___y_2123_ = v___x_2371_;
                    v___y_2124_ = v_unsafeGet_2296_;
                    v___y_2125_ = v___x_2302_;
                    v___y_2126_ = v___x_2308_;
                    v___y_2127_ = v___x_2318_;
                    v___y_2128_ = v___x_2365_;
                    v___y_2129_ = v___x_2395_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_2288_);
                    v___x_2396_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29;
                    leanh::lean_inc(v_quotContext_2289_);
                    leanh::lean_inc(v_currMacroScope_2290_);
                    v___y_2078_ = v_sz_2358_;
                    v___y_2079_ = v_mk_2292_;
                    v___y_2080_ = v___x_2356_;
                    v___y_2081_ = v___x_2313_;
                    v___y_2082_ = v___x_2350_;
                    v___y_2083_ = v_instCoeMk_2294_;
                    v___y_2084_ = v___x_2310_;
                    v___y_2085_ = v___x_2383_;
                    v___y_2086_ = v___x_2311_;
                    v___y_2087_ = v___x_2343_;
                    v___y_2088_ = v___x_2346_;
                    v___y_2089_ = v___x_2301_;
                    v___y_2090_ = v___x_2315_;
                    v___y_2091_ = v___x_2316_;
                    v___y_2092_ = v_currMacroScope_2290_;
                    v___y_2093_ = v___x_2373_;
                    v___y_2094_ = v___x_2347_;
                    v___y_2095_ = v___x_2368_;
                    v___y_2096_ = v___x_2349_;
                    v___y_2097_ = v___x_2307_;
                    v___y_2098_ = v___x_2319_;
                    v___y_2099_ = v___x_2363_;
                    v___y_2100_ = v_instCoeGet_2297_;
                    v___y_2101_ = v___x_2353_;
                    v___y_2102_ = v___x_2366_;
                    v___y_2103_ = v___x_2393_;
                    v___y_2104_ = v___x_2357_;
                    v___y_2105_ = v_quotContext_2289_;
                    v___y_2106_ = v___x_2303_;
                    v___y_2107_ = v___x_2355_;
                    v___y_2108_ = v___x_2344_;
                    v___y_2109_ = v___x_2330_;
                    v___y_2110_ = v___x_2348_;
                    v___y_2111_ = v___x_2312_;
                    v___y_2112_ = v___x_2352_;
                    v___y_2113_ = v_get_2295_;
                    v___y_2114_ = v___x_2380_;
                    v___y_2115_ = v___x_2381_;
                    v___y_2116_ = v___x_2323_;
                    v___y_2117_ = v___x_2323_;
                    v___y_2118_ = v___x_2309_;
                    v___y_2119_ = v___x_2299_;
                    v___y_2120_ = v___x_2387_;
                    v___y_2121_ = v___x_2359_;
                    v___y_2122_ = v___x_2300_;
                    v___y_2123_ = v___x_2371_;
                    v___y_2124_ = v_unsafeGet_2296_;
                    v___y_2125_ = v___x_2302_;
                    v___y_2126_ = v___x_2308_;
                    v___y_2127_ = v___x_2318_;
                    v___y_2128_ = v___x_2365_;
                    v___y_2129_ = v___x_2396_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2402_ == 0 {
                    v___x_2404_ = v___x_2401_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2405_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_val_2399_);
                    v___x_2404_ = v_reuseFailAlloc_2405_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2288_ = v___x_2404_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___boxed(
    mut v_x_2407_: *mut leanh::LeanObject,
    mut v_a_2408_: *mut leanh::LeanObject,
    mut v_a_2409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2410_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1(
            v_x_2407_, v_a_2408_, v_a_2409_,
        );
    leanh::lean_dec_ref(v_a_2408_);
    return v_res_2410_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_OpaqueType(
    builtin: u8,
) -> *mut leanh::LeanObject {
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
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_OpaqueType(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Util_Binder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_OpaqueType(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Binder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_OpaqueType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_OpaqueType(builtin);
}